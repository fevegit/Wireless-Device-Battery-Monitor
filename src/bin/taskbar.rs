//! BatteryHub Taskbar. Runs in the background (the installer can add it to autostart)
//! and draws "🎧 25%  🖱 32%" straight onto the taskbar, left of the notification area, so no
//! hovering is needed. Levels reload every minute. Left click does nothing; right click opens the
//! menu (warning levels, refresh options, exit). When the taskbar cannot host the strip (vertical
//! taskbar, unknown Explorer layout) it falls back to one notification-area icon per device.
#![windows_subsystem = "windows"]

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::ffi::c_void;
use std::rc::Rc;
use std::time::Instant;

use batteryhub::cardfx::{BlurScratch, CardBg, CardContent, Layer, compose_card};
use batteryhub::device::Missing;
use batteryhub::i18n::{n_, tr, trf};
use batteryhub::settings;
use batteryhub::stats::fmt_hours;
use batteryhub::ui::{self, rgb, split};
use batteryhub::{DeviceKind, DeviceStatus};
use windows::Win32::Foundation::{COLORREF, ERROR_ALREADY_EXISTS, GetLastError, HANDLE, HWND, LPARAM, LRESULT, POINT, RECT, SIZE, WPARAM};
use windows::Win32::Graphics::Gdi::*;
use windows::Win32::System::LibraryLoader::GetModuleHandleW;
use windows::Win32::System::Threading::{CreateMutexW, GetCurrentProcess, SetProcessWorkingSetSize};
use windows::Win32::UI::Controls::{
    TOOLTIPS_CLASSW, TTF_ABSOLUTE, TTF_TRACK, TTM_ADDTOOLW, TTM_GETBUBBLESIZE, TTM_SETMAXTIPWIDTH, TTM_TRACKACTIVATE, TTM_TRACKPOSITION, TTM_UPDATETIPTEXTW, TTS_ALWAYSTIP, TTS_NOPREFIX, TTTOOLINFOW,
};
use windows::Win32::UI::HiDpi::{DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2, GetDpiForWindow, SetProcessDpiAwarenessContext};
use windows::Win32::UI::Input::KeyboardAndMouse::{TME_LEAVE, TRACKMOUSEEVENT, TrackMouseEvent};
use windows::Win32::UI::Shell::{
    NIF_ICON, NIF_INFO, NIF_MESSAGE, NIF_SHOWTIP, NIF_TIP, NIIF_INFO, NIIF_WARNING, NIM_ADD, NIM_DELETE, NIM_MODIFY, NOTIFYICONDATAW, Shell_NotifyIconW,
};
use windows::Win32::UI::WindowsAndMessaging::*;
use windows::core::w;

const WM_POLL_DONE: u32 = WM_APP + 2;
const WM_TRAY: u32 = WM_APP + 3;
const WM_QUICK_DONE: u32 = WM_APP + 4;
const WM_UPDATE_CHECKED: u32 = WM_APP + 5;
const WM_UPDATE_DOWNLOADED: u32 = WM_APP + 6;
const WM_SHOW_UPDATED: u32 = WM_APP + 7;
/// tray_probe found where a secondary taskbar's notification area begins.
const WM_TRAY_PROBED: u32 = WM_APP + 8;
/// Another window came to the front: copies over a full-screen window step aside at once.
const WM_FOREGROUND: u32 = WM_APP + 20;
/// A background write of the history finished (wparam: 1 = written).
const WM_HISTORY_SAVED: u32 = WM_APP + 9;
// Not exported by the windows crate's WindowsAndMessaging module.
const WM_MOUSELEAVE: u32 = 0x02A3;
const TIMER_POLL: usize = 1;
const TIMER_PLACE: usize = 2;
const TIMER_DEVCHANGE: usize = 3;
const TIMER_BTWATCH: usize = 4;
const TIMER_QUICK: usize = 5;
const TIMER_AUTO_UPDATE: usize = 6;
/// "Update finished" message shortly after the first start of an updated version.
const TIMER_UPDATED: usize = 7;
/// Frames of the hover card's fade / slide (~60 per second while it runs).
const TIMER_CARD: usize = 20;
/// Removes the low-battery notification's temporary icon.
const TIMER_NOTIFY: usize = 21;
/// While the mouse is off the strip with the card open: is it on the card, or gone?
const TIMER_AWAY: usize = 22;
/// Devices sliding to their new places on the strip.
const TIMER_SLIDE: usize = 23;
/// Frames of a strip popping in as it appears on a monitor, or out as it leaves one.
const TIMER_MIRROR_IN: usize = 24;
/// Frames of the widget gliding to a new place or height (GLIDE_MS).
const TIMER_GLIDE: usize = 25;
/// "Widget position: left": the taskbar's left end checked again soon after a window opens or
/// closes (its task button comes or goes), LEFT_PROBES times.
const TIMER_LEFT_PROBE: usize = 26;
const LEFT_PROBES: u8 = 4;
/// How old the taskbar's items may be when checking room for the widget: next to the icons they
/// move all the time; next to the clock only a window opening or closing changes the room (the
/// shell hook marks the answer stale then), so this is only a fallback.
const ROOM_LEFT_AGE: std::time::Duration = std::time::Duration::from_secs(2);
const ROOM_AGE: std::time::Duration = std::time::Duration::from_secs(60);
/// Length of that glide.
const GLIDE_MS: f32 = 260.0;
/// Length of that pop-in.
const MIRROR_IN_MS: f32 = 320.0;
/// How long a device takes to slide to its new place (ms).
const SLIDE_MS: f32 = 220.0;
/// An item appearing on the strip first opens its space (the others move aside), then pops in;
/// one leaving pops out, then its space closes. Durations in ms.
const SPACE_MS: f32 = 200.0;
const POP_MS: f32 = 260.0;
/// Items appearing together pop in one after another, this far apart (ms).
const STAGGER_MS: u64 = 70;
/// Key of the "no devices found" glyph on the strip.
const NONE_KEY: &str = "\u{0}none";
/// The refresh glyph's item while a refresh started from the menu runs.
const REFRESH_KEY: &str = "\u{0}refresh";

/// An item appearing on or leaving the strip.
struct Presence {
    leaving: bool,
    /// When it started (later than now while it waits for its turn).
    at: Instant,
}

impl Presence {
    /// (share of its width it takes 0-1, how far it has popped in 0-1, finished).
    fn frame(&self) -> (f32, f32, bool) {
        let t = self.at.elapsed().as_secs_f32() * 1000.0;
        let ease = |v: f32| {
            let v = v.clamp(0.0, 1.0);
            v * v * (3.0 - 2.0 * v)
        };
        if self.leaving {
            (1.0 - ease((t - POP_MS) / SPACE_MS), 1.0 - (t / POP_MS).clamp(0.0, 1.0), t >= POP_MS + SPACE_MS)
        } else {
            (ease(t / SPACE_MS), ((t - SPACE_MS) / POP_MS).clamp(0.0, 1.0), t >= SPACE_MS + POP_MS)
        }
    }

    /// Turns around halfway (a device that comes back while leaving, or goes while appearing),
    /// from about where it is now.
    fn turn(&mut self, leaving: bool) {
        if self.leaving == leaving {
            return;
        }
        let (f, p, _) = self.frame();
        let t = match (leaving, p > 0.0) {
            (true, true) => POP_MS * (1.0 - p),
            (true, false) => POP_MS + SPACE_MS * (1.0 - f),
            (false, true) => SPACE_MS + POP_MS * p,
            (false, false) => SPACE_MS * f,
        };
        self.leaving = leaving;
        self.at = Instant::now().checked_sub(std::time::Duration::from_secs_f32(t / 1000.0)).unwrap_or_else(Instant::now);
    }
}

/// One item on the strip this frame.
struct Item {
    key: String,
    /// The device (None for the "no devices found" glyph).
    dev: Option<DeviceStatus>,
    /// Its place among the visible devices (hit-testing); None while it leaves.
    vis: Option<usize>,
    /// Share of its width it takes, and how far it has popped in.
    f: f32,
    p: f32,
}
/// Notification-area id of the low-battery notification (device icons use hashes of their keys).
const NOTIFY_UID: u32 = 0x5BA7;
/// The app's own notification-area icon, shown while no device is and the empty-strip icon is off.
const APP_UID: u32 = 0x5BA8;
const CARD_SHOW_MS: f32 = 160.0;
const CARD_HIDE_MS: f32 = 110.0;
/// How long the mouse may be off both the strip and the card before the card closes.
const CARD_AWAY_MS: u128 = 300;
/// Old and new card blending when the mouse moves to another device (like the taskbar's previews).
const CARD_CROSS_MS: f32 = 130.0;
/// Strongest blur of the card's content during its animations (px at 100 % scaling).
const BLUR_MAX: f32 = 6.0;
/// Automatic update check this long after start-up; when the network is not up yet (e.g. right
/// at sign-in) it is tried again every AUTO_UPDATE_RETRY_MS, at most AUTO_UPDATE_RETRIES times.
const AUTO_UPDATE_DELAY_MS: u32 = 2_000;
const AUTO_UPDATE_RETRY_MS: u32 = 15_000;
const AUTO_UPDATE_RETRIES: u32 = 8;
/// The right-click menu is open: the strip shows no hover card meanwhile.
static MENU_OPEN: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
static AUTO_UPDATE_TRIES: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
/// How often receivers whose device is off or asleep are checked again.
const QUICK_MS: u32 = 10_000;
const WM_DEVICECHANGE_MSG: u32 = 0x0219;
const DBT_DEVNODES_CHANGED: usize = 0x0007;
const DBT_DEVICEARRIVAL: usize = 0x8000;
const DBT_DEVICEREMOVECOMPLETE: usize = 0x8004;
/// Seconds the strip may be impossible to place before falling back to notification-area icons.
const FALLBACK_AFTER_TICKS: u32 = 3;
const PBT_APMRESUMEAUTOMATIC: usize = 0x0012;
const PBT_APMSUSPEND: usize = 0x0004;
/// Battery refresh intervals offered in the menu, in minutes.
const INTERVALS: [(u32, &str); 5] = [(1, n_("1 minute")), (5, n_("5 minutes")), (10, n_("10 minutes")), (30, n_("30 minutes")), (60, n_("1 hour"))];
/// 30..34: menu ids 10 / 11 belong to ID_ICONS_MODE / ID_VERSIONS (issue #171).
const ID_INTERVAL_BASE: usize = 30;
const ID_ON_CHANGE: usize = 20;
const MIN_GRACE_SEC: u64 = 150;
const ID_EXIT: usize = 1;
const ID_REFRESH_DEVICES: usize = 2;
const ID_REFRESH_LEVELS: usize = 3;
const ID_CHECK_UPDATES: usize = 4;
const ID_REQUEST: usize = 5;
const ID_AUTOSTART: usize = 6;
const ID_AUTO_UPDATE: usize = 7;
const ID_BACKGROUND: usize = 8;
const ID_SILENT_UPDATE: usize = 9;
const ID_ICONS_MODE: usize = 10;
const ID_VERSIONS: usize = 11;
const ID_DASHBOARD: usize = 12;
const ID_COMPACT: usize = 13;
const _: () = assert!(ID_INTERVAL_BASE > ID_ON_CHANGE && ID_INTERVAL_BASE + INTERVALS.len() <= ID_MONITOR_ALL, "menu ids overlap");
/// "Show widget on": all monitors, main monitor only, or ID_MONITOR_FIRST + i for one other monitor.
const ID_MONITOR_ALL: usize = 40;
const ID_MONITOR_MAIN: usize = 41;
const ID_MONITOR_FIRST: usize = 42;
const ID_MONITOR_GONE: usize = 73;
/// "Position on the taskbar": ID_POSITION_FIRST + i for POSITION_OFFSETS[i].
const ID_POSITION_FIRST: usize = 80;
const ID_POSITION_CUSTOM: usize = 95;
/// 10 px further left / right (any value, not only the listed ones).
const ID_POSITION_LEFT: usize = 96;
const ID_POSITION_RIGHT: usize = 97;
/// "Widget position": next to the clock (right) or next to the taskbar icons (left).
const ID_SIDE_RIGHT: usize = 98;
const ID_SIDE_LEFT: usize = 99;
/// "Widget position: next to the icons": right after the task buttons, wherever they are.
const ID_SIDE_ICONS: usize = 118;
/// "Help": the GitHub page and ID_HELP_RELEASE_FIRST + i for the latest releases.
const ID_HELP_GITHUB: usize = 200;
const ID_HELP_RELEASE_FIRST: usize = 201;
const HELP_RELEASES: usize = 5;
const ID_HELP_DISCORD: usize = 207;
/// The project's Discord server (a permanent invite).
const DISCORD_URL: &str = "https://discord.gg/aVp2E7a9tb";
/// "BatteryHub is free and will stay free": opens the page for a tip.
const ID_HELP_FREE: usize = 208;
const SUPPORT_URL: &str = "https://revolut.me/p2ps";
/// "Show the icon when no device is connected".
const ID_SHOW_EMPTY: usize = 210;
const POSITION_MAX: u32 = 1000;
const POSITION_OFFSETS: [u32; 11] = [0, 20, 40, 60, 80, 100, 120, 140, 160, 180, 200];
/// "Height on the taskbar": ID_HEIGHT_FIRST + i for HEIGHT_OFFSETS[i] (px, + = down).
const ID_HEIGHT_FIRST: usize = 100;
const ID_HEIGHT_CUSTOM: usize = 115;
const ID_HEIGHT_UP: usize = 116;
const ID_HEIGHT_DOWN: usize = 117;
const HEIGHT_MAX: i32 = 40;
const HEIGHT_OFFSETS: [i32; 7] = [-15, -10, -5, 0, 5, 10, 15];
/// "Language": Windows' language, create a new one, open the folder, or ID_LANG_FIRST + i.
const ID_LANG_AUTO: usize = 120;
const ID_LANG_NEW: usize = 121;
const ID_LANG_FOLDER: usize = 122;
const ID_LANG_FIRST: usize = 130;
const ID_LANG_LAST: usize = 199;
const _: () = assert!(
    ID_POSITION_RIGHT < ID_HEIGHT_FIRST && ID_HEIGHT_DOWN < ID_LANG_AUTO && ID_HEIGHT_CUSTOM < ID_LANG_AUTO && ID_LANG_LAST < settings::MENU_BASE,
    "menu ids overlap"
);

pub const MAIN_CLASS: windows::core::PCWSTR = w!("BatteryHub.Taskbar.Main");
const STRIP_CLASS: windows::core::PCWSTR = w!("BatteryHub.Taskbar.Strip");
const SETTINGS_KEY: &str = batteryhub::install::TASKBAR.settings_key;
/// Folder name of this edition's data (%LOCALAPPDATA%\BatteryHub\Taskbar).
const EDITION: &str = batteryhub::install::TASKBAR.short;

/// BH_PROFILE (measurements only): time spent on the hover card, written to the debug log
/// (%TEMP%h2.log, with BH_DEBUG) each time the card closes.
mod prof {
    use std::sync::atomic::{AtomicU64, Ordering};
    pub static FRAMES: AtomicU64 = AtomicU64::new(0);
    pub static COMPOSE_US: AtomicU64 = AtomicU64::new(0);
    pub static PRESENT_US: AtomicU64 = AtomicU64::new(0);
    pub static RENDERS: AtomicU64 = AtomicU64::new(0);
    pub static RENDER_US: AtomicU64 = AtomicU64::new(0);
    pub fn add(c: &AtomicU64, v: u64) {
        c.fetch_add(v, Ordering::Relaxed);
    }
    pub fn report() {
        if std::env::var_os("BH_PROFILE").is_none() {
            return;
        }
        let g = |c: &AtomicU64| c.load(Ordering::Relaxed);
        let f = g(&FRAMES).max(1);
        super::dbg_log(&format!(
            "card profile: {} frames, compose {} us/frame, present {} us/frame, {} renders ({} us each)",
            g(&FRAMES),
            g(&COMPOSE_US) / f,
            g(&PRESENT_US) / f,
            g(&RENDERS),
            g(&RENDER_US) / g(&RENDERS).max(1)
        ));
    }
}

/// BH_DEMO (diagnostics and measurements only): two made-up devices on the strip, so the hover
/// card can be tried and measured without devices at hand. They are never written to the history.
fn demo_devices() -> Vec<DeviceStatus> {
    if std::env::var_os("BH_DEMO").is_none() {
        return Vec::new();
    }
    let dev = |key: &str, name: &str, kind: DeviceKind, percent: i32, charging: bool| DeviceStatus {
        key: key.into(),
        name: name.into(),
        via: "Demo (BH_DEMO)".into(),
        kind,
        percent,
        charging,
        ..Default::default()
    };
    vec![dev("demo:headset", "Demo headset", DeviceKind::Headset, 38, true), dev("demo:mouse", "Demo mouse with a longer name", DeviceKind::Mouse, 64, false)]
}

/// A dashboard window is open (it shows the history file, so that is kept current).
fn dashboard_open() -> bool {
    batteryhub::dashboard::any_open()
}

fn history_path() -> std::path::PathBuf {
    batteryhub::history::History::path(EDITION)
}

/// A notification-area icon to show: device key, text, colour, level, tooltip and optional glyph.
type TrayIcon = (String, String, COLORREF, i32, String, Option<char>);

struct Tracked {
    status: DeviceStatus,
    seen: Instant,
    /// The name the device reports (status.name is the user's name for it, if it has one).
    reported: String,
}

#[derive(Default)]
struct App {
    main: HWND,
    strip: HWND,
    taskbar: HWND,
    devices: BTreeMap<String, Tracked>,
    order: Vec<String>,
    polling: bool,
    loaded: bool,
    /// A refresh started from the menu: show the ↻ indicator until it finishes.
    manual: bool,
    /// "Refresh devices": forget every known device (no grace period) on the next result.
    forget: bool,
    /// Devices whose status line is saved for the dashboard this session: (name, kind, via).
    known_saved: HashMap<String, (String, u8, String)>,
    /// Whether the devices were enumerated at least once (the first read always enumerates).
    scanned: bool,
    /// The next poll was triggered by a device connecting / disconnecting: devices that are gone
    /// and have no sleep grace period disappear at once instead of after MIN_GRACE_SEC.
    devchange: bool,
    size: SIZE,
    last_place: (RECT, RECT, i32),
    /// Main strip uses a topmost popup owned by `Shell_TrayWnd` (e.g. when Start11's SDTaskbar
    /// sits inside `Shell_TrayWnd` and fights child-window Z-order).
    strip_popup: bool,
    /// Main taskbar's notification area, to notice when it changes (see tray_probe).
    main_tray: RECT,
    /// Every copy on another monitor knows its place: the strips appear on all taskbars together.
    mirrors_ready: bool,
    /// Strips popping in or out (strip, start, leaving): copies on other monitors, and the main
    /// strip when the widget moves to or from another monitor. A copy that left is destroyed, the
    /// main strip hidden, once it has popped out.
    mirror_in: Vec<(HWND, Instant, bool)>,
    /// Hidden copies kept ready on taskbars that don't show the widget (taskbar, strip). A window
    /// created at the moment it is needed loses its first updates (its pop-in stalled, or it
    /// stayed blank), so a copy is made ahead of time and reused when the widget comes back.
    parked: Vec<(HWND, HWND)>,
    /// Strip x ranges of the devices drawn in the last paint: (from, to, device index).
    hits: Vec<(i32, i32, usize)>,
    /// Hover tooltip (tracking tooltip owned by the main window) and what it shows right now.
    tip: HWND,
    /// Hover card (device, level, last 24 hours) and the levels it charts.
    card: HWND,
    card_anim: CardAnim,
    /// Rendered card contents of the last two devices shown (moving back and forth between two
    /// devices reuses them instead of drawing the text and chart again).
    card_cache: Vec<Rc<CardContent>>,
    /// The card's bitmap, kept while the card is open (one allocation, not one per frame).
    card_surface: Option<Surface>,
    /// Scratch buffers of the card's blur, kept while the card is open.
    blur_scratch: BlurScratch,
    /// Hour picked on the card's chart with the mouse (device key, time): its level and change
    /// are shown above the chart.
    card_scrub: Option<(String, u64)>,
    /// Top and bottom of the card's chart (card pixels), to map the mouse to a time.
    card_chart_y: (i32, i32),
    /// Since when the mouse is on neither the strip nor the card: the card closes shortly after,
    /// so the mouse can move from the strip onto it.
    card_away: Option<Instant>,
    /// Fonts of the strip and the card for the current DPI scale.
    fonts: Option<Fonts>,
    history: batteryhub::history::History,
    /// Last time the history was written.
    history_saved: Option<Instant>,
    tip_for: Option<usize>,
    tracking: bool,
    taskbar_created: u32,
    /// (taskbar client height, DPI, light theme) the strip was last rendered for; a change (e.g.
    /// after leaving full screen, a DPI or theme change) triggers a fresh render.
    painted_for: (i32, u32, bool),
    /// Notification-area icons instead of the strip (the taskbar cannot host it right now).
    fallback: bool,
    /// The taskbar is on the left or right edge: the strip is a column (icon over level, devices
    /// stacked) above the notification area, and hit ranges are along y.
    vertical: bool,
    /// Consecutive seconds the strip could not be placed.
    fail_ticks: u32,
    /// Fallback icons: device key -> (icon id, icon handle).
    tray: BTreeMap<String, (u32, HICON)>,
    /// Last Bluetooth connection signature (connect / disconnect detection).
    bt_sig: u64,
    /// A device change arrived while a read was running: read again as soon as it finishes.
    pending_change: bool,
    /// Receivers / cables (vid, pid) whose device reported "off" in the last read.
    offline_hw: HashSet<(u16, u16)>,
    /// Light taskbar theme and the optional extra gap (TaskbarOffset), read once and again only
    /// when Windows reports a settings change - not from the registry every second.
    light: bool,
    offset: u32,
    /// Up / down shift of the widget in px (TaskbarOffsetY, + = down).
    offset_y: i32,
    /// The height shift gliding to offset_y: (shift it started from, when).
    y_glide: Option<(f32, Instant)>,
    /// The strip gliding to a new place (taskbar client coordinates): (from, to, when).
    glide: Option<(POINT, POINT, Instant)>,
    /// Copies on other monitors gliding to a new place (screen coordinates): (copy, from, to, when).
    mirror_glides: RefCell<Vec<(HWND, POINT, POINT, Instant)>>,
    /// Checks of the taskbar's left end left after a window opened or closed.
    left_probes: u8,
    /// Per taskbar: whether the widget fits there without covering a task button (false: hidden
    /// there). Taskbars missing here have room as far as known.
    rooms: RefCell<HashMap<isize, bool>>,
    /// No taskbar the widget is shown on has room: the levels are notification-area icons.
    crowded: bool,
    /// Phones with "Rising level means charging": (last level, charging as worked out).
    rising: HashMap<String, (i32, bool)>,
    /// When "not enough room" was last said (once per crowding, at most every 10 minutes).
    crowded_said: Option<Instant>,
    /// "SHELLHOOK" message: windows opening and closing.
    shell_msg: u32,
    /// Copies of the strip on the taskbars of other monitors ("Show widget on"): (taskbar, strip).
    mirrors: Vec<(HWND, HWND)>,
    /// Pixels of the last render, pushed to every mirror as well.
    pixels: Vec<u32>,
    /// The same render on the hover plate (made once per render, not on every hover).
    lit: Vec<u32>,
    /// Strip the tooltip belongs to (the main strip or a mirror).
    tip_on: HWND,
    /// Strip under the mouse: drawn with the taskbar's hover plate.
    hovered: HWND,
    /// "Show widget on": "all", "main" or the id of one other monitor (cached setting).
    choice: String,
    /// The widget is shown only on another monitor: the main taskbar's strip is hidden.
    primary_hidden: bool,
    /// Plate behind the widget for transparent taskbars (cached setting).
    background: bool,
    /// "Show as notification-area icons": Windows places and orders the icons (no strip).
    icons_mode: bool,
    /// "Widget position: left": next to the taskbar icons instead of the clock (horizontal taskbars).
    align_left: bool,
    /// With align_left: right after the last task button (also centred ones), not at the left end.
    after_icons: bool,
    /// "Show the icon when no device is connected" turned off: nothing on the strip then, and the
    /// app's own notification-area icon (APP_UID) holds the menu.
    hide_empty: bool,
    app_icon: Option<HICON>,
    compact: bool,
    /// Version the setup just updated from (shown once in "Update finished").
    updated_from: Option<String>,
    /// Names chosen with "Rename device" (device key -> name).
    names: std::collections::HashMap<String, String>,
    /// Keys of the devices with "Show on the taskbar" turned off.
    hidden: HashSet<String>,
    /// "Warn at 5%" state per device.
    critical: settings::CriticalWarnings,
    /// Icon of the low-battery notification while it is shown.
    notify_icon: Option<HICON>,
    /// Registered message: a device was renamed.
    names_msg: u32,
    /// Device order chosen by the user (dragged on the strip, or "Move left / right").
    saved_order: Vec<String>,
    /// Key of the device being dragged along the strip (left button held).
    drag: Option<String>,
    /// While dragging: the mouse along the strip, and where in the device it was grabbed.
    drag_at: i32,
    grab: i32,
    /// Where each device starts along the strip in the last render: its place, and where it was
    /// drawn (moving devices are drawn away from their place).
    starts: std::collections::HashMap<String, i32>,
    drawn_at: std::collections::HashMap<String, f32>,
    /// Devices sliding to a new place: distance still to go when it started, and when.
    slides: std::collections::HashMap<String, (f32, Instant)>,
    /// The order changed since the last render: devices slide from where they were drawn.
    reordered: bool,
    /// When each device was last written as seen, and when unseen devices were last forgotten.
    seen_saved: std::collections::HashMap<String, u64>,
    forgot_at: u64,
    /// Items appearing on or leaving the strip, and the items of the last render (with the
    /// device as it was, so one that left can still pop out).
    presence: std::collections::HashMap<String, Presence>,
    shown: Vec<(String, Option<DeviceStatus>)>,
    /// Length of the strip in the last render (width, or height on a vertical taskbar).
    strip_len: i32,
}

thread_local! {
    static APP: RefCell<App> = RefCell::new(App::default());
    /// Receivers being read by the running quick read.
    static QUICK_IDS: RefCell<Vec<(u16, u16)>> = const { RefCell::new(Vec::new()) };
}

fn with_app<R>(f: impl FnOnce(&mut App) -> R) -> Option<R> {
    APP.with(|a| a.try_borrow_mut().ok().map(|mut a| f(&mut a)))
}

/// The time picked on the card's chart for a mouse at `t`: the nearest whole hour (local time)
/// within 12 hours of now, or now itself.
fn snap_hour(t: f64, now: u64) -> u64 {
    let l = batteryhub::dashboard::local(now);
    let base = now - (l.minute as u64 * 60 + l.second as u64);
    let (lo, hi) = (now.saturating_sub(12 * 3600), now + 12 * 3600);
    (-13i64..=13)
        .map(|k| (base as i64 + k * 3600) as u64)
        .filter(|h| (lo..=hi).contains(h))
        .chain(std::iter::once(now))
        .min_by(|a, b| (*a as f64 - t).abs().total_cmp(&(*b as f64 - t).abs()))
        .unwrap_or(now)
}

/// A change of level for the card: "−2%", "+5%", "−0.4%" (tenths below 1 %, with the language's
/// decimal separator), "±0%".
fn fmt_change(d: f64) -> String {
    let a = d.abs();
    if a < 0.05 {
        return "±0%".into(); // rounds to 0.0
    }
    let num = if a < 0.95 { batteryhub::i18n::decimal(a, 1) } else { format!("{a:.0}") };
    if d < 0.0 { format!("−{num}%") } else { format!("+{num}%") }
}

// ---- drawing -----------------------------------------------------------------------------------

/// Premultiplied BGRA canvas.
struct Canvas {
    w: i32,
    h: i32,
    px: Vec<u32>,
}

impl Canvas {
    /// Filled rounded rectangle [x0, x1) x [y0, y1).
    #[allow(clippy::too_many_arguments)]
    fn fill_rrect(&mut self, x0: i32, y0: i32, x1: i32, y1: i32, radius: i32, c: COLORREF, a: u32) {
        let r = radius.max(0).min((x1 - x0) / 2).min((y1 - y0) / 2);
        for y in y0..y1 {
            for x in x0..x1 {
                let dx = if x < x0 + r {
                    x0 + r - x
                } else if x >= x1 - r {
                    x - (x1 - r - 1)
                } else {
                    0
                };
                let dy = if y < y0 + r {
                    y0 + r - y
                } else if y >= y1 - r {
                    y - (y1 - r - 1)
                } else {
                    0
                };
                if dx * dx + dy * dy <= r * r {
                    self.blend(x, y, c, a);
                }
            }
        }
    }

    /// Filled circle.
    fn disc(&mut self, cx: i32, cy: i32, r: i32, c: COLORREF) {
        let r = r.max(1);
        for y in cy - r..=cy + r {
            for x in cx - r..=cx + r {
                if (x - cx) * (x - cx) + (y - cy) * (y - cy) <= r * r {
                    self.blend(x, y, c, 255);
                }
            }
        }
    }

    /// Straight line of thickness `t` (horizontal and vertical lines are what the chart needs).
    fn line(&mut self, x0: i32, y0: i32, x1: i32, y1: i32, t: i32, c: COLORREF) {
        let steps = (x1 - x0).abs().max((y1 - y0).abs()).max(1);
        let half = (t / 2).max(0);
        for i in 0..=steps {
            let x = x0 + (x1 - x0) * i / steps;
            let y = y0 + (y1 - y0) * i / steps;
            for oy in -half..t - half {
                for ox in -half..t - half {
                    self.blend(x + ox, y + oy, c, 255);
                }
            }
        }
    }

    /// Dashed straight line (the card's forecast): dashes and gaps of `dash` px along it.
    #[allow(clippy::too_many_arguments)]
    fn dashed(&mut self, x0: i32, y0: i32, x1: i32, y1: i32, t: i32, c: COLORREF, dash: i32) {
        let steps = (x1 - x0).abs().max((y1 - y0).abs()).max(1);
        let dash = dash.max(2);
        let half = (t / 2).max(0);
        for i in 0..=steps {
            if (i / dash) % 2 == 1 {
                continue;
            }
            let x = x0 + (x1 - x0) * i / steps;
            let y = y0 + (y1 - y0) * i / steps;
            for oy in -half..t - half {
                for ox in -half..t - half {
                    self.blend(x + ox, y + oy, c, 255);
                }
            }
        }
    }

    /// Text mask at (x, y).
    fn draw(&mut self, m: &Mask, x: i32, y: i32, c: COLORREF, alpha: u32) {
        for yy in 0..m.h {
            for xx in 0..m.w {
                let a = m.a[(yy * m.w + xx) as usize] as u32 * alpha / 255;
                self.blend(x + xx, y + yy, c, a);
            }
        }
    }

    /// Fills the canvas with a rounded rectangle, `inset` from the top and bottom edge.
    fn round_rect(&mut self, inset: i32, radius: i32, c: COLORREF, a: u32) {
        let (w, h, r) = (self.w, self.h, radius.max(1));
        for y in inset..h - inset {
            for x in 0..w {
                let dx = if x < r {
                    r - x
                } else if x >= w - r {
                    x - (w - r - 1)
                } else {
                    0
                };
                let dy = if y < inset + r {
                    inset + r - y
                } else if y >= h - inset - r {
                    y - (h - inset - r - 1)
                } else {
                    0
                };
                if dx * dx + dy * dy <= r * r {
                    self.blend(x, y, c, a);
                }
            }
        }
    }

    fn blend(&mut self, x: i32, y: i32, c: COLORREF, a: u32) {
        if x < 0 || y < 0 || x >= self.w || y >= self.h || a == 0 {
            return;
        }
        let (r, g, b) = split(c);
        let d = &mut self.px[(y * self.w + x) as usize];
        let inv = 255 - a;
        let ch = |src: u8, shift: u32| ((src as u32 * a + ((*d >> shift) & 0xFF) * inv) / 255) & 0xFF;
        let na = (a + ((*d >> 24) & 0xFF) * inv / 255).min(255);
        *d = na << 24 | ch(r, 16) << 16 | ch(g, 8) << 8 | ch(b, 0);
    }
}

/// Ink coverage of `text`, cropped to the drawn pixels. Same technique as the original widget:
/// ClearType text, white on black (black on white for a light taskbar), coverage = RGB average.
struct Mask {
    w: i32,
    h: i32,
    a: Vec<u8>,
}

fn mask(text: &str, font: HFONT, dark_on_light: bool) -> Mask {
    unsafe {
        let dc = CreateCompatibleDC(None);
        let old_f = SelectObject(dc, HGDIOBJ(font.0));
        let wtext: Vec<u16> = text.encode_utf16().collect();
        let mut sz = SIZE::default();
        let _ = GetTextExtentPoint32W(dc, &wtext, &mut sz);
        let (w, h) = (sz.cx + 8, sz.cy + 8);
        let bmi = BITMAPINFO {
            bmiHeader: BITMAPINFOHEADER {
                biSize: size_of::<BITMAPINFOHEADER>() as u32,
                biWidth: w,
                biHeight: -h,
                biPlanes: 1,
                biBitCount: 32,
                biCompression: BI_RGB.0,
                ..Default::default()
            },
            ..Default::default()
        };
        let mut bits: *mut c_void = std::ptr::null_mut();
        let mut out = Mask { w: 0, h: 0, a: Vec::new() };
        if let Ok(bmp) = CreateDIBSection(Some(dc), &bmi, DIB_RGB_COLORS, &mut bits, None, 0) {
            let old_b = SelectObject(dc, HGDIOBJ(bmp.0));
            let px = std::slice::from_raw_parts_mut(bits as *mut u32, (w * h) as usize);
            px.fill(if dark_on_light { 0xFFFF_FFFF } else { 0 });
            SetBkMode(dc, TRANSPARENT);
            SetTextColor(dc, if dark_on_light { rgb(0, 0, 0) } else { rgb(255, 255, 255) });
            let _ = TextOutW(dc, 4, 4, &wtext);
            let _ = GdiFlush();
            let cover = |v: u32| -> u8 {
                let c = ((v & 0xFF) + ((v >> 8) & 0xFF) + ((v >> 16) & 0xFF)) / 3;
                (if dark_on_light { 255 - c } else { c }) as u8
            };
            let (mut x0, mut y0, mut x1, mut y1) = (w, h, -1, -1);
            for y in 0..h {
                for x in 0..w {
                    if cover(px[(y * w + x) as usize]) != 0 {
                        x0 = x0.min(x);
                        x1 = x1.max(x);
                        y0 = y0.min(y);
                        y1 = y1.max(y);
                    }
                }
            }
            if x1 >= 0 {
                out.w = x1 - x0 + 1;
                out.h = y1 - y0 + 1;
                out.a = Vec::with_capacity((out.w * out.h) as usize);
                for y in 0..out.h {
                    for x in 0..out.w {
                        out.a.push(cover(px[((y0 + y) * w + x0 + x) as usize]));
                    }
                }
            }
            SelectObject(dc, old_b);
            let _ = DeleteObject(HGDIOBJ(bmp.0));
        }
        SelectObject(dc, old_f);
        let _ = DeleteDC(dc);
        out
    }
}

/// Creates a ClearType font, falling back when the preferred face is not installed (GDI would
/// otherwise silently substitute another face).
fn make_font(px: i32, weight: i32, face: &str, fallback: &str, fallback_px: i32) -> HFONT {
    for (f, size) in [(face, px), (fallback, if fallback_px > 0 { fallback_px } else { px })] {
        unsafe {
            let h = CreateFontW(
                -size,
                0,
                0,
                0,
                weight,
                0,
                0,
                0,
                DEFAULT_CHARSET,
                OUT_DEFAULT_PRECIS,
                CLIP_DEFAULT_PRECIS,
                CLEARTYPE_QUALITY,
                0,
                &windows::core::HSTRING::from(f),
            );
            if f == fallback {
                return h;
            }
            let dc = CreateCompatibleDC(None);
            let o = SelectObject(dc, HGDIOBJ(h.0));
            let mut got = [0u16; 64];
            GetTextFaceW(dc, Some(&mut got));
            SelectObject(dc, o);
            let _ = DeleteDC(dc);
            if batteryhub::util::from_wide(&got).eq_ignore_ascii_case(f) {
                return h;
            }
            let _ = DeleteObject(HGDIOBJ(h.0));
        }
    }
    unreachable!()
}

/// Earbuds icon (drawn, no font has one): two buds outlined, `h` px tall. A bud that is not
/// reported (in its case, or off) is grey, like a sleeping device.
fn buds_mask(h: i32, left_on: bool, right_on: bool) -> Mask {
    let n = h.max(8);
    Mask { w: n, h: n, a: batteryhub::gui::earbuds_icon(n, left_on, right_on) }
}

/// A premultiplied BGRA image (w x h) scaled by `k` around its centre, box-blurred with radius
/// `blur` (twice, close to a Gaussian) and faded to `fade`: one frame of a copy popping in.
fn pop_pixels(src: &[u32], w: usize, h: usize, k: f32, blur: usize, fade: f32) -> Vec<u32> {
    if src.len() != w * h || w == 0 || h == 0 {
        return src.to_vec();
    }
    let ch = |p: u32, i: u32| ((p >> (8 * i)) & 0xFF) as f32;
    let (cx, cy) = (w as f32 / 2.0, h as f32 / 2.0);
    let at = |x: i32, y: i32| if x < 0 || y < 0 || x >= w as i32 || y >= h as i32 { 0 } else { src[y as usize * w + x as usize] };
    let mut img = vec![[0f32; 4]; w * h];
    for y in 0..h {
        let sy = cy + (y as f32 + 0.5 - cy) / k - 0.5;
        let (y0, fy) = (sy.floor() as i32, sy - sy.floor());
        for x in 0..w {
            let sx = cx + (x as f32 + 0.5 - cx) / k - 0.5;
            let (x0, fx) = (sx.floor() as i32, sx - sx.floor());
            let (a, b, c, d) = (at(x0, y0), at(x0 + 1, y0), at(x0, y0 + 1), at(x0 + 1, y0 + 1));
            let o = &mut img[y * w + x];
            for (i, v) in o.iter_mut().enumerate() {
                let i = i as u32;
                let top = ch(a, i) * (1.0 - fx) + ch(b, i) * fx;
                let bottom = ch(c, i) * (1.0 - fx) + ch(d, i) * fx;
                *v = top * (1.0 - fy) + bottom * fy;
            }
        }
    }
    if blur > 0 {
        let r = blur as i32;
        let mut tmp = vec![[0f32; 4]; w.max(h)];
        for horizontal in [true, false, true, false] {
            let (lines, len) = if horizontal { (h, w) } else { (w, h) };
            for line in 0..lines {
                let idx = |i: usize| if horizontal { line * w + i } else { i * w + line };
                for i in 0..len {
                    tmp[i] = img[idx(i)];
                }
                for i in 0..len as i32 {
                    let mut sum = [0f32; 4];
                    for j in (i - r).max(0)..=(i + r).min(len as i32 - 1) {
                        for (s, v) in sum.iter_mut().zip(tmp[j as usize]) {
                            *s += v;
                        }
                    }
                    img[idx(i as usize)] = sum.map(|v| v / (2 * r + 1) as f32);
                }
            }
        }
    }
    img.iter()
        .map(|p| {
            let c = |i: usize| ((p[i] * fade).round().clamp(0.0, 255.0) as u32) << (8 * i);
            c(0) | c(1) | c(2) | c(3)
        })
        .collect()
}

/// `top` over `bottom` with `gap` px between, both centred.
fn stack_masks(top: &Mask, bottom: &Mask, gap: i32) -> Mask {
    let w = top.w.max(bottom.w);
    let h = top.h + gap + bottom.h;
    let mut a = vec![0u8; (w * h) as usize];
    for (m, y0) in [(top, 0), (bottom, top.h + gap)] {
        let x0 = (w - m.w) / 2;
        for y in 0..m.h {
            let src = &m.a[(y * m.w) as usize..((y + 1) * m.w) as usize];
            let at = ((y0 + y) * w + x0) as usize;
            a[at..at + m.w as usize].copy_from_slice(src);
        }
    }
    Mask { w, h, a }
}

/// Bilinear scaling of a mask by `k`.
fn scale_mask(m: &Mask, k: f32) -> Mask {
    let w = ((m.w as f32 * k).round() as i32).max(1);
    let h = ((m.h as f32 * k).round() as i32).max(1);
    let at = |x: i32, y: i32| if x < 0 || y < 0 || x >= m.w || y >= m.h { 0.0 } else { m.a[(y * m.w + x) as usize] as f32 };
    let mut a = Vec::with_capacity((w * h) as usize);
    for y in 0..h {
        let sy = (y as f32 + 0.5) / k - 0.5;
        let (y0, fy) = (sy.floor() as i32, sy - sy.floor());
        for x in 0..w {
            let sx = (x as f32 + 0.5) / k - 0.5;
            let (x0, fx) = (sx.floor() as i32, sx - sx.floor());
            let top = at(x0, y0) * (1.0 - fx) + at(x0 + 1, y0) * fx;
            let bottom = at(x0, y0 + 1) * (1.0 - fx) + at(x0 + 1, y0 + 1) * fx;
            a.push((top * (1.0 - fy) + bottom * fy).round().clamp(0.0, 255.0) as u8);
        }
    }
    Mask { w, h, a }
}

/// Draws a piece of an item popping in (`p` 0 to 1) or out (1 to 0): it grows from half its size
/// around the item's centre `c` with a small overshoot, fades in, and is blurred while it moves
/// (strongest at the start), like the strip's other motion.
#[allow(clippy::too_many_arguments)]
fn draw_popping(cv: &mut Canvas, m: &Mask, at: (i32, i32), c: (f32, f32), p: f32, s: f32, color: COLORREF, alpha: u32) {
    if p <= 0.0 {
        return;
    }
    let (c1, c3) = (1.70158f32, 2.70158f32);
    let back = 1.0 + c3 * (p - 1.0).powi(3) + c1 * (p - 1.0).powi(2);
    let k = (0.5 + 0.5 * back).max(0.05);
    let sm = scale_mask(m, k);
    let blur = ((1.0 - p) * (1.0 - p) * 4.0 * s).round() as i32;
    let sm = if blur > 0 { blur_mask(&blur_mask(&sm, blur, true), blur, false) } else { sm };
    // Where the piece's centre goes, scaled towards the item's centre.
    let (mx, my) = (at.0 as f32 + m.w as f32 / 2.0, at.1 as f32 + m.h as f32 / 2.0);
    let (nx, ny) = (c.0 + (mx - c.0) * k, c.1 + (my - c.1) * k);
    let fade = p * p * (3.0 - 2.0 * p);
    cv.draw(&sm, (nx - sm.w as f32 / 2.0).round() as i32, (ny - sm.h as f32 / 2.0).round() as i32, color, (alpha as f32 * fade).round() as u32);
}

/// Box blur (twice, close to a Gaussian) of a mask along x or y; the result is 2 * r larger on
/// that axis.
fn blur_mask(m: &Mask, r: i32, horizontal: bool) -> Mask {
    let (w, h) = if horizontal { (m.w + 2 * r, m.h) } else { (m.w, m.h + 2 * r) };
    let mut a = vec![0u32; (w * h) as usize];
    for y in 0..m.h {
        for x in 0..m.w {
            let (tx, ty) = if horizontal { (x + r, y) } else { (x, y + r) };
            a[(ty * w + tx) as usize] = m.a[(y * m.w + x) as usize] as u32;
        }
    }
    let (lines, len) = if horizontal { (h, w) } else { (w, h) };
    let at = |line: i32, i: i32| if horizontal { (line * w + i) as usize } else { (i * w + line) as usize };
    let mut tmp = vec![0u32; len as usize];
    for _ in 0..2 {
        for line in 0..lines {
            for i in 0..len {
                tmp[i as usize] = a[at(line, i)];
            }
            for i in 0..len {
                let (lo, hi) = ((i - r).max(0), (i + r).min(len - 1));
                let sum: u32 = (lo..=hi).map(|j| tmp[j as usize]).sum();
                a[at(line, i)] = sum / (2 * r + 1) as u32;
            }
        }
    }
    Mask { w, h, a: a.into_iter().map(|v| v.min(255) as u8).collect() }
}

/// The icon of a device on the strip and the card: its glyph, or the drawn earbuds.
fn device_icon(d: &DeviceStatus, font: HFONT, light: bool) -> Mask {
    if d.kind != DeviceKind::Earbuds {
        return mask(&d.kind.glyph().to_string(), font, light);
    }
    let g = mask(&DeviceKind::Headset.glyph().to_string(), font, light);
    let (l, r) = d.buds.map(|b| (b.left >= 0, b.right >= 0)).unwrap_or((true, true));
    // Rows with ink in the headset glyph: the earbuds take the same top and bottom.
    let ink: Vec<i32> = (0..g.h).filter(|&y| (0..g.w).any(|x| g.a[(y * g.w + x) as usize] > 60)).collect();
    let (Some(&top), Some(&bottom)) = (ink.first(), ink.last()) else { return buds_mask(g.h, l, r) };
    let (ink_top, ink_bottom) = batteryhub::gui::EARBUDS_INK;
    let n = (((bottom - top + 1) as f32) / (ink_bottom - ink_top)).round() as i32;
    let b = buds_mask(n, l, r);
    let dy = top - (ink_top * n as f32).round() as i32;
    let mut a = vec![0u8; (b.w * g.h) as usize];
    for y in 0..b.h {
        let ty = y + dy;
        if (0..g.h).contains(&ty) {
            a[(ty * b.w) as usize..((ty + 1) * b.w) as usize].copy_from_slice(&b.a[(y * b.w) as usize..((y + 1) * b.w) as usize]);
        }
    }
    Mask { w: b.w, h: g.h, a }
}

struct Piece {
    /// Index of the device this piece belongs to (for hover hit-testing), None for others.
    dev: Option<usize>,
    m: Mask,
    color: COLORREF,
    alpha: u32,
    gap_after: i32,
    /// Part of the piece drawn in another colour (same size as `m`, drawn at the same place):
    /// earbuds whose two buds are coloured apart.
    second: Option<(Mask, COLORREF)>,
}

impl Piece {
    fn new(dev: Option<usize>, m: Mask, color: COLORREF, alpha: u32, gap_after: i32) -> Self {
        Piece { dev, m, color, alpha, gap_after, second: None }
    }

    /// The piece's masks with their colours.
    fn layers(&self) -> impl Iterator<Item = (&Mask, COLORREF)> {
        std::iter::once((&self.m, self.color)).chain(self.second.as_ref().map(|(m, c)| (m, *c)))
    }

    /// The same piece in two colours: `first` before column (or row) `at`, `second` from it on.
    fn split(dev: Option<usize>, m: Mask, at: i32, rows: bool, colors: (COLORREF, COLORREF), alpha: u32, gap_after: i32) -> Self {
        if colors.0 == colors.1 {
            return Piece::new(dev, m, colors.0, alpha, gap_after);
        }
        let (a, b) = split_mask(&m, at, rows);
        Piece { dev, m: a, color: colors.0, alpha, gap_after, second: Some((b, colors.1)) }
    }
}

/// Two masks of `m`'s size: the ink before column (or row) `at`, and the ink from it on.
fn split_mask(m: &Mask, at: i32, rows: bool) -> (Mask, Mask) {
    let mut a = m.a.clone();
    let mut b = m.a.clone();
    for y in 0..m.h {
        for x in 0..m.w {
            let i = (y * m.w + x) as usize;
            if (if rows { y } else { x }) < at {
                b[i] = 0;
            } else {
                a[i] = 0;
            }
        }
    }
    (Mask { w: m.w, h: m.h, a }, Mask { w: m.w, h: m.h, a: b })
}

/// Every font the strip and the card draw with, for one DPI scale (creating a font and checking
/// its face costs a device context each time, so they are made once, not per render).
struct Fonts {
    scale: f32,
    icons: HFONT,
    bolt: HFONT,
    text: HFONT,
    card_icon: HFONT,
    card_name: HFONT,
    card_big: HFONT,
    card_small: HFONT,
}

impl Fonts {
    fn new(s: f32) -> Self {
        let px = |v: f32| (v * s).round() as i32;
        Fonts {
            scale: s,
            icons: make_font(px(16.0), 400, "Segoe Fluent Icons", "Segoe MDL2 Assets", 0),
            bolt: make_font(px(11.0), 400, "Segoe Fluent Icons", "Segoe MDL2 Assets", 0),
            text: make_font(px(13.0), 400, "Segoe UI Variable Text", "Segoe UI", px(12.0)),
            card_icon: make_font(px(16.0), 400, "Segoe Fluent Icons", "Segoe MDL2 Assets", 0),
            card_name: make_font(px(15.0), 600, "Segoe UI Variable Text", "Segoe UI", 0),
            card_big: make_font(px(30.0), 600, "Segoe UI Variable Display", "Segoe UI", 0),
            card_small: make_font(px(12.0), 400, "Segoe UI Variable Text", "Segoe UI", 0),
        }
    }
}

impl Drop for Fonts {
    fn drop(&mut self) {
        for f in [self.icons, self.bolt, self.text, self.card_icon, self.card_name, self.card_big, self.card_small] {
            unsafe {
                let _ = DeleteObject(HGDIOBJ(f.0));
            }
        }
    }
}

impl App {
    /// Creates the fonts for the current DPI scale when there are none yet or the scale changed.
    fn ensure_fonts(&mut self) {
        let s = self.scale();
        if self.fonts.as_ref().map(|f| f.scale) != Some(s) {
            self.fonts = Some(Fonts::new(s));
        }
    }

    /// Device `i` of the strip (connected devices in strip order), without copying the list.
    fn visible_at(&self, i: usize) -> Option<&DeviceStatus> {
        self.order.iter().filter_map(|k| self.devices.get(k)).map(|t| &t.status).filter(|s| s.connected && !self.hidden.contains(&s.key)).nth(i)
    }

    fn scale(&self) -> f32 {
        let dpi = unsafe { GetDpiForWindow(self.taskbar) };
        if dpi == 0 { 1.0 } else { dpi as f32 / 96.0 }
    }

    /// Connected devices shown on the taskbar ("Show on the taskbar" not turned off).
    fn visible(&self) -> Vec<DeviceStatus> {
        self.connected().into_iter().filter(|s| !self.hidden.contains(&s.key)).collect()
    }

    /// Every connected device, hidden ones too (the right-click menu lists them all).
    fn connected(&self) -> Vec<DeviceStatus> {
        self.order.iter().filter_map(|k| self.devices.get(k)).map(|t| t.status.clone()).filter(|s| s.connected).collect()
    }

    /// Renders the strip and hands it to the layered window.
    fn paint(&mut self) {
        if self.crowded && !self.fallback {
            self.sync_tray();
        }
        if self.fallback {
            self.sync_tray();
            return;
        }
        if self.strip.0.is_null() {
            return;
        }
        self.painted_for = self.render_target();
        let s = self.scale();
        let px = |v: f32| (v * s).round() as i32;
        let light = self.light;
        // Same colours, fonts and spacing as the original C++ widget.
        let fg = if light { rgb(0, 0, 0) } else { rgb(255, 255, 255) };
        let red = ui::low_color(light);
        self.ensure_fonts();
        let (icons, bolt, text) = self.fonts.as_ref().map(|f| (f.icons, f.bolt, f.text)).unwrap_or_default();

        let mut pieces: Vec<Piece> = Vec::new();
        let devices = self.visible();
        let items = self.strip_items(&devices);
        for (i, it) in items.iter().enumerate() {
            let Some(d) = &it.dev else {
                if it.key == REFRESH_KEY {
                    // Refresh started from the menu: a small refresh glyph until it finishes.
                    pieces.push(Piece::new(Some(i), mask("\u{E72C}", bolt, light), fg, 170, 0));
                } else {
                    // Battery-unknown glyph, so there is always something to right-click.
                    pieces.push(Piece::new(Some(i), mask("\u{E996}", icons, light), fg, 110, 0));
                }
                continue;
            };
            let alpha = if d.asleep { 120 } else { 255 };
            // Red at or below this device's own warning level (right-click menu, default 15%);
            // earbuds by each bud's own level. The icon too when the device's menu asks for it.
            let threshold = settings::threshold(SETTINGS_KEY, &d.key);
            let low = settings::is_low(d, threshold);
            let buds_low = settings::buds_low(d, threshold);
            let red_icon = settings::red_icon(SETTINGS_KEY, &d.key);
            let tint = |on: bool| if on { red } else { fg };
            // The icon in its own colour (menu: Icon colour), red over it when asked for.
            let own = settings::icon_rgb(settings::icon_color(SETTINGS_KEY, &d.key), d.vid).map(|(r, g, b)| rgb(r, g, b)).unwrap_or(fg);
            let icon_tint = |on: bool| if red_icon && on { red } else { own };
            // Lightning bolt on power: green while charging, blue once it reached 100%.
            let bolt_color = ui::bolt_color(d, light);
            let mark = bolt_color.is_some();
            let icon = device_icon(d, icons, light);
            let icon_piece = match buds_low {
                // Each bud of the drawn earbuds in its own colour (left bud in the left half).
                Some((l, r)) if d.kind == DeviceKind::Earbuds => {
                    let half = icon.w / 2;
                    Piece::split(Some(i), icon, half, false, (icon_tint(l), icon_tint(r)), alpha, px(5.0))
                }
                _ => Piece::new(Some(i), icon, icon_tint(low), alpha, px(5.0)),
            };
            pieces.push(icon_piece);
            let gap = if mark { px(2.0) } else { 0 };
            let both = d.buds.filter(|b| d.percent >= 0 && b.left >= 0 && b.right >= 0);
            let piece = match both {
                // Earbuds with both buds out: each bud's own level, each red on its own. On a
                // vertical taskbar the two don't fit side by side: left over right.
                Some(b) => {
                    let (l, r) = buds_low.unwrap_or((low, low));
                    let (ml, mr) = (mask(&format!("{}%", b.left), text, light), mask(&format!("{}%", b.right), text, light));
                    if self.vertical {
                        let at = ml.h;
                        Piece::split(Some(i), stack_masks(&ml, &mr, px(1.0)), at, true, (tint(l), tint(r)), alpha, gap)
                    } else {
                        let m = mask(&format!("{}% {}%", b.left, b.right), text, light);
                        let at = ml.w + (m.w - ml.w - mr.w).max(0) / 2;
                        Piece::split(Some(i), m, at, false, (tint(l), tint(r)), alpha, gap)
                    }
                }
                None => {
                    let t = if !d.level_text.is_empty() && d.percent < 0 {
                        d.level_text.clone()
                    } else if d.percent >= 0 {
                        format!("{}%", d.percent)
                    } else {
                        "?".into()
                    };
                    Piece::new(Some(i), mask(&t, text, light), tint(low), alpha, gap)
                }
            };
            pieces.push(piece);
            if let Some(c) = bolt_color {
                pieces.push(Piece::new(Some(i), mask("\u{E945}", bolt, light), c, alpha, 0));
            }
        }
        // The refresh glyph is an item of its own (strip_items): it pops in and out like a device.
        let refresh = false;
        let mut tb = RECT::default();
        unsafe {
            let _ = GetClientRect(self.taskbar, &mut tb);
        }
        if self.vertical {
            self.paint_column(&pieces, &items, refresh, (tb.right - tb.left).clamp(px(32.0), px(160.0)), s, light);
            return;
        }
        let h = (tb.bottom - tb.top).clamp(px(24.0), px(64.0));
        // The padding comes and goes with the first item and the last one.
        let fmax = items.iter().map(|it| it.f).fold(if refresh { 1.0 } else { 0.0 }, f32::max);
        let pad = px(8.0) as f32 * fmax;
        let dev_gap = px(14.0) as f32;
        // Lay out: each item at its full width, taking only its share of it (the ones after it
        // follow at once), so a device appearing makes room before it pops in.
        let n = items.len();
        let compact = self.compact && pieces.iter().all(|p| p.m.h * 2 + px(1.0) <= h);
        let mut xs = vec![0i32; pieces.len()];
        let mut ys = vec![None; pieces.len()];
        let mut ranges: Vec<(i32, i32)> = vec![(0, 0); n];
        let mut x = pad;
        let mut k = 0;
        for i in 0..n {
            if i > 0 {
                x += dev_gap * items[i - 1].f.min(items[i].f);
            }
            let start = x.round() as i32;
            let mut cx = 0;
            let first = k;
            while k < pieces.len() && pieces[k].dev == Some(i) {
                xs[k] = start + cx;
                cx += pieces[k].m.w + if pieces.get(k + 1).is_some_and(|q| q.dev == Some(i)) { pieces[k].gap_after } else { 0 };
                k += 1;
            }
            if compact
                && k > first + 1 {
                    let icon = &pieces[first];
                    let row_start = icon.m.w + icon.gap_after;
                    let row_w = cx - row_start;
                    let row_h = pieces[first + 1..k].iter().map(|p| p.m.h).max().unwrap_or(0);
                    let gap = px(1.0);
                    let y = (h - icon.m.h - gap - row_h) / 2;
                    cx = icon.m.w.max(row_w);
                    xs[first] = start + (cx - icon.m.w) / 2;
                    ys[first] = Some(y);
                    for j in first + 1..k {
                        xs[j] += (cx - row_w) / 2 - row_start;
                        ys[j] = Some(y + icon.m.h + gap + (row_h - pieces[j].m.h) / 2);
                    }
                }
            ranges[i] = (start, start + cx);
            x += cx as f32 * items[i].f;
        }
        for xk in xs.iter_mut().skip(k) {
            x += px(10.0) as f32 * fmax.min(if n > 0 { 1.0 } else { 0.0 });
            *xk = x.round() as i32;
            x += pieces[k].m.w as f32;
        }
        let w = ((x + pad).round() as i32).max(1);
        // Alpha 1 everywhere: fully transparent pixels of a layered window let clicks fall through.
        let mut cv = Canvas { w, h, px: vec![0x0100_0000; (w * h) as usize] };
        if self.background {
            // Rounded plate in the taskbar's own colour: keeps the text readable on a transparent
            // or restyled taskbar (e.g. TranslucentTB, Windhawk's Taskbar Styler).
            let plate = if light { rgb(243, 243, 243) } else { rgb(32, 32, 32) };
            cv.round_rect(px(4.0), px(6.0), plate, 235);
        }
        // Each visible device owns its pieces plus half of the gap around them.
        self.hits.clear();
        for (i, it) in items.iter().enumerate() {
            if let Some(v) = it.vis {
                let from = self.hits.last().map(|h| h.1).unwrap_or(0);
                self.hits.push((from, ranges[i].1 + (dev_gap / 2.0) as i32, v));
            }
        }
        let keys: Vec<String> = items.iter().map(|it| it.key.clone()).collect();
        let moves = self.motion(&keys, &ranges, w, s);
        let shift_y = self.shown_offset_y();
        // The dragged device last, over the others.
        let held = |p: &Piece| p.dev.is_some_and(|i| moves[i].2 < 255);
        for pass in [false, true] {
            for ((p, &x), &y) in pieces.iter().zip(&xs).zip(&ys) {
                if held(p) != pass {
                    continue;
                }
                let (off, blur, alpha) = p.dev.map(|i| moves[i]).unwrap_or((0, 0, 255));
                let y0 = (y.unwrap_or((h - p.m.h) / 2) + px(shift_y)).clamp(0, (h - p.m.h).max(0));
                for (m, color) in p.layers() {
                    if let Some(i) = p.dev
                        && items[i].p < 1.0
                    {
                        let c = ((ranges[i].0 + ranges[i].1) as f32 / 2.0 + off as f32, h as f32 / 2.0);
                        draw_popping(&mut cv, m, (x + off, y0), c, items[i].p, s, color, p.alpha);
                    } else if blur > 0 {
                        let b = blur_mask(m, blur, true);
                        cv.draw(&b, x + off - blur, y0, color, p.alpha * alpha / 255);
                    } else {
                        cv.draw(m, x + off, y0, color, p.alpha * alpha / 255);
                    }
                }
            }
        }
        if let Some(last) = self.hits.last_mut() {
            last.1 = w;
        }
        let resized = self.size.cx != w || self.size.cy != h;
        self.size = SIZE { cx: w, cy: h };
        self.pixels = cv.px;
        self.lit = self.hover_pixels();
        if !self.popping(self.strip) {
            self.push(self.strip);
        }
        // Same size: the copies get the new image here. A new size: their placement below gives
        // it to them together with their new place.
        if !resized {
            for i in 0..self.mirrors.len() {
                let m = self.mirrors[i].1;
                if !self.popping(m) {
                    self.push(m);
                }
            }
        }
        for i in 0..self.parked.len() {
            let m = self.parked[i].1;
            if !self.popping(m) {
                self.push(m);
            }
        }
        if !resized && (self.drag.is_some() || !self.slides.is_empty() || !self.presence.is_empty() || self.y_glide.is_some()) {
            return; // an animation frame: same size, same place
        }
        self.last_place.2 = -1; // force a reposition with the new width
        self.place();
        // The copies keep their left edge when their width changes: move them too, so their right
        // edge stays next to the clock (not only at the next timer tick).
        for i in 0..self.mirrors.len() {
            self.place_mirror_at(i);
        }
    }

    /// Vertical taskbar: each device as its icon over its level (the bolt beside the level when it
    /// fits), devices stacked, as wide as the taskbar. Hit ranges are rows (y).
    fn paint_column(&mut self, pieces: &[Piece], items: &[Item], refresh: bool, w: i32, s: f32, light: bool) {
        let px = |v: f32| (v * s).round() as i32;
        let sizes: Vec<(Option<usize>, i32, i32)> = pieces.iter().map(|p| (p.dev, p.m.w, p.m.h)).collect();
        let (pad, dev_gap) = (px(8.0), px(12.0));
        let (placed, full_h, rows) = column_layout(&sizes, w, pad, px(2.0), dev_gap, px(2.0));
        let n = items.len();
        let mut ranges: Vec<(i32, i32)> = vec![(i32::MAX, 0); n];
        for (p, &(_, y, show)) in pieces.iter().zip(&placed) {
            if let (Some(i), true) = (p.dev, show) {
                ranges[i] = (ranges[i].0.min(y), ranges[i].1.max(y + p.m.h));
            }
        }
        // What each item gives back of its height while it appears or leaves: the items below it
        // move up by what the ones above gave back (the column stays on the notification area).
        let fmax = items.iter().map(|it| it.f).fold(if refresh { 1.0 } else { 0.0 }, f32::max);
        let mut gone = (1.0 - fmax) * pad as f32;
        let mut shift = vec![0i32; n];
        for i in 0..n {
            shift[i] = gone.round() as i32;
            gone += (1.0 - items[i].f) * (ranges[i].1 - ranges[i].0).max(0) as f32;
            if i + 1 < n {
                gone += (1.0 - items[i].f.min(items[i + 1].f)) * dev_gap as f32;
            }
        }
        let tail = gone.round() as i32;
        let h = (full_h - tail - ((1.0 - fmax) * pad as f32).round() as i32).max(1);
        for (i, r) in ranges.iter_mut().enumerate() {
            *r = (r.0 - shift[i], r.1 - shift[i]);
        }
        let ys: Vec<i32> = pieces.iter().zip(&placed).map(|(p, &(_, y, _))| y - p.dev.map(|i| shift[i]).unwrap_or(tail)).collect();
        let mut hits: Vec<(i32, i32, usize)> = rows.iter().filter_map(|&(a, b, i)| items[i].vis.map(|v| (a - shift[i], b - shift[i], v))).collect();
        if let Some(first) = hits.first_mut() {
            first.0 = 0;
        }
        if let Some(last) = hits.last_mut() {
            last.1 = h;
        }
        let mut cv = Canvas { w, h, px: vec![0x0100_0000; (w * h) as usize] };
        if self.background {
            let plate = if light { rgb(243, 243, 243) } else { rgb(32, 32, 32) };
            cv.round_rect(0, px(6.0), plate, 235);
        }
        let keys: Vec<String> = items.iter().map(|it| it.key.clone()).collect();
        let moves = self.motion(&keys, &ranges, h, s);
        let held = |p: &Piece| p.dev.is_some_and(|i| moves[i].2 < 255);
        for pass in [false, true] {
            for ((p, &(x, _, show)), &y) in pieces.iter().zip(&placed).zip(&ys) {
                if !show || held(p) != pass {
                    continue;
                }
                let (off, blur, alpha) = p.dev.map(|i| moves[i]).unwrap_or((0, 0, 255));
                for (m, color) in p.layers() {
                    if let Some(i) = p.dev
                        && items[i].p < 1.0
                    {
                        let c = (w as f32 / 2.0, (ranges[i].0 + ranges[i].1) as f32 / 2.0 + off as f32);
                        draw_popping(&mut cv, m, (x, y + off), c, items[i].p, s, color, p.alpha);
                    } else if blur > 0 {
                        cv.draw(&blur_mask(m, blur, false), x, y + off - blur, color, p.alpha * alpha / 255);
                    } else {
                        cv.draw(m, x, y + off, color, p.alpha * alpha / 255);
                    }
                }
            }
        }
        self.hits = hits;
        let resized = self.size.cx != w || self.size.cy != h;
        self.size = SIZE { cx: w, cy: h };
        self.pixels = cv.px;
        self.lit = self.hover_pixels();
        if !self.popping(self.strip) {
            self.push(self.strip);
        }
        // The copies on other monitors too (they only got the image at the once-a-second
        // placement before, so their animations stuttered). A new size: their placement gives it
        // to them together with their new place.
        if !resized {
            for i in 0..self.mirrors.len() {
                let m = self.mirrors[i].1;
                if !self.popping(m) {
                    self.push(m);
                }
            }
        }
        for i in 0..self.parked.len() {
            let m = self.parked[i].1;
            if !self.popping(m) {
                self.push(m);
            }
        }
        if !resized && (self.drag.is_some() || !self.slides.is_empty() || !self.presence.is_empty() || self.y_glide.is_some()) {
            return; // an animation frame: same size, same place
        }
        self.last_place.2 = -1;
        self.place();
        for i in 0..self.mirrors.len() {
            self.place_mirror_at(i);
        }
    }

    /// The last render on the taskbar's hover plate: a rounded, slightly lighter (dark taskbar) or
    /// darker (light taskbar) rectangle behind the content, like the taskbar's own buttons.
    fn hover_pixels(&self) -> Vec<u32> {
        let (w, h) = (self.size.cx, self.size.cy);
        let s = self.scale();
        let mut plate = Canvas { w, h, px: vec![0; (w * h) as usize] };
        let (color, alpha) = if self.light { (rgb(0, 0, 0), 14) } else { (rgb(255, 255, 255), 21) };
        plate.round_rect((4.0 * s).round() as i32, (4.0 * s).round() as i32, color, alpha);
        self.pixels
            .iter()
            .zip(&plate.px)
            .map(|(&c, &p)| {
                // Content over the plate, both premultiplied.
                let inv = 255 - (c >> 24);
                let ch = |sh: u32| (((c >> sh) & 0xFF) + ((p >> sh) & 0xFF) * inv / 255).min(255);
                ch(24) << 24 | ch(16) << 16 | ch(8) << 8 | ch(0)
            })
            .collect()
    }

    /// Shows or removes the hover plate when the mouse enters or leaves a strip.
    fn set_hovered(&mut self, on: HWND) {
        if on == self.hovered {
            return;
        }
        let old = std::mem::replace(&mut self.hovered, on);
        for strip in [old, on] {
            if !strip.0.is_null() && is_our_strip(strip) {
                self.push(strip);
            }
        }
    }

    /// Hands the last render to a strip window (the main strip or a mirror).
    fn push(&self, strip: HWND) {
        if strip == self.hovered && self.lit.len() == self.pixels.len() {
            self.push_px(strip, &self.lit);
        } else {
            self.push_px(strip, &self.pixels);
        }
    }

    /// Shows `px` (premultiplied, the strip's size) in `strip`.
    fn push_px(&self, strip: HWND, px: &[u32]) {
        self.push_px_at(strip, px, None);
    }

    /// Like push_px, and moves the window to `at` (screen) in the same step: a copy that changes
    /// size and place shows the new image in the new place at once, never for a frame in between.
    fn push_px_at(&self, strip: HWND, px: &[u32], at: Option<POINT>) {
        let (w, h) = (self.size.cx, self.size.cy);
        if strip.0.is_null() || px.len() != (w * h) as usize {
            return;
        }
        unsafe {
            let screen = GetDC(None);
            let mem = CreateCompatibleDC(Some(screen));
            let bmi = BITMAPINFO {
                bmiHeader: BITMAPINFOHEADER {
                    biSize: size_of::<BITMAPINFOHEADER>() as u32,
                    biWidth: w,
                    biHeight: -h,
                    biPlanes: 1,
                    biBitCount: 32,
                    biCompression: BI_RGB.0,
                    ..Default::default()
                },
                ..Default::default()
            };
            let mut bits: *mut c_void = std::ptr::null_mut();
            if let Ok(bmp) = CreateDIBSection(Some(mem), &bmi, DIB_RGB_COLORS, &mut bits, None, 0) {
                std::ptr::copy_nonoverlapping(px.as_ptr(), bits as *mut u32, px.len());
                let ob = SelectObject(mem, HGDIOBJ(bmp.0));
                let src = POINT::default();
                let bf = BLENDFUNCTION { BlendOp: AC_SRC_OVER as u8, BlendFlags: 0, SourceConstantAlpha: 255, AlphaFormat: AC_SRC_ALPHA as u8 };
                let _ = UpdateLayeredWindow(strip, Some(screen), at.as_ref().map(|p| p as *const POINT), Some(&self.size), Some(mem), Some(&src), COLORREF(0), Some(&bf), ULW_ALPHA);
                SelectObject(mem, ob);
                let _ = DeleteObject(HGDIOBJ(bmp.0));
            }
            let _ = DeleteDC(mem);
            ReleaseDC(None, screen);
        }
    }

    // ---- taskbar placement ---------------------------------------------------------------------

    /// What the strip has to be rendered for right now: taskbar height, DPI and theme.
    fn render_target(&self) -> (i32, u32, bool) {
        let mut client = RECT::default();
        unsafe {
            let _ = GetClientRect(self.taskbar, &mut client);
            ((client.right - client.left) << 12 | (client.bottom - client.top), GetDpiForWindow(self.taskbar), self.light)
        }
    }

    /// Creates the strip as a child of the taskbar (again, after Explorer restarted). Returns false
    /// when the taskbar cannot host it right now: no taskbar / notification area (Explorer is
    /// restarting or uses an unknown layout), or a vertical taskbar.
    fn ensure_strip(&mut self) -> bool {
        unsafe {
            // The strip is only valid while it still is a window and a child of a live taskbar; a
            // handle that outlived Explorer can be reused by an unrelated window.
            let alive = !self.strip.0.is_null()
                && IsWindow(Some(self.strip)).as_bool()
                && IsWindow(Some(self.taskbar)).as_bool()
                && has_sdtaskbar(self.taskbar) == self.strip_popup
                && if self.strip_popup {
                    GetWindow(self.strip, GW_OWNER).is_ok_and(|p| p == self.taskbar)
                } else {
                    GetParent(self.strip).is_ok_and(|p| p == self.taskbar)
                };
            if !alive {
                if is_our_strip(self.strip) {
                    let _ = DestroyWindow(self.strip);
                }
                self.strip = HWND::default();
                self.strip_popup = false;
                let Ok(taskbar) = FindWindowW(w!("Shell_TrayWnd"), None) else {
                    dbg_log("no Shell_TrayWnd");
                    return false;
                };
                if FindWindowExW(Some(taskbar), None, w!("TrayNotifyWnd"), None).is_err() {
                    dbg_log("no TrayNotifyWnd");
                    return false;
                }
                self.taskbar = taskbar;
            }
            let mut bar = RECT::default();
            let _ = GetWindowRect(self.taskbar, &mut bar);
            let vertical = bar.bottom - bar.top > bar.right - bar.left;
            if vertical != self.vertical {
                // Turned between horizontal and vertical: lay the strip out again.
                self.vertical = vertical;
                self.painted_for = Default::default();
                self.last_place = Default::default();
            }
            if alive {
                return true;
            }
            let popup = has_sdtaskbar(self.taskbar);
            let Some(strip) = (if popup { create_copy(self.taskbar) } else { create_strip(self.taskbar) }) else {
                return false;
            };
            dbg_log(&format!("strip created {:?} parent {:?} popup {}", strip, self.taskbar, popup));
            self.strip = strip;
            self.strip_popup = popup;
            self.last_place = Default::default();
            // Shown only on another monitor: the new main strip stays hidden from the start (no
            // flash on the main taskbar before the first sync hides it).
            self.primary_hidden = self.chosen_bars().1;
        }
        if !self.fallback {
            self.paint();
            // While copies on other monitors still wait for their place, place() shows it with them.
            if !self.primary_hidden
                && self.mirrors_ready
                && !(self.strip_popup && unsafe { fullscreen_over(self.taskbar) || !IsWindowVisible(self.taskbar).as_bool() })
            {
                unsafe {
                    let _ = ShowWindow(self.strip, SW_SHOWNOACTIVATE);
                }
            }
        }
        true
    }

    /// Destroys any other strip window of this process on the taskbar (only `self.strip` may exist).
    fn remove_orphan_strips(&self) {
        unsafe {
            let mut after: Option<HWND> = None;
            while let Ok(h) = FindWindowExW(Some(self.taskbar), after, STRIP_CLASS, None) {
                if h.0.is_null() {
                    break;
                }
                after = Some(h);
                if h != self.strip && is_our_strip(h) {
                    dbg_log(&format!("removing orphaned strip {h:?}"));
                    let _ = DestroyWindow(h);
                }
            }
        }
    }

    /// Switches between the taskbar strip and notification-area icons.
    fn set_fallback(&mut self, on: bool) {
        if self.fallback == on {
            return;
        }
        dbg_log(&format!("fallback to notification-area icons: {on}"));
        self.fallback = on;
        // Recomputed by the next tick (sync_crowded) once the strip is back.
        self.crowded = false;
        if on {
            self.hide_tip();
            self.drop_mirrors();
            if !self.strip.0.is_null() {
                unsafe {
                    let _ = ShowWindow(self.strip, SW_HIDE);
                }
            }
            self.sync_tray();
        } else {
            self.remove_tray();
            self.last_place = Default::default();
            self.paint();
        }
    }

    /// One tick of the 1 s placement timer: keep the strip in place, or fall back.
    fn tick(&mut self) {
        if std::env::var_os("BH_FORCE_FALLBACK").is_some() {
            return;
        }
        if self.icons_mode {
            // Notification-area icons by choice: Windows owns their place and order.
            if !self.fallback {
                self.set_fallback(true);
            }
            return;
        }
        if self.ensure_strip() {
            self.remove_orphan_strips();
            self.fail_ticks = 0;
            if self.fallback {
                self.set_fallback(false);
            }
            // Re-render when the taskbar changed height, DPI or theme since the last render
            // (e.g. after leaving a full-screen game).
            if self.render_target() != self.painted_for {
                self.paint();
            } else {
                self.place();
            }
            self.sync_mirrors();
            self.sync_crowded();
            self.sync_app_icon();
        } else {
            self.fail_ticks += 1;
            if self.fail_ticks >= FALLBACK_AFTER_TICKS {
                self.set_fallback(true);
            }
        }
    }

    /// No taskbar the widget is shown on has room beside its task buttons: the levels move to
    /// notification-area icons (said once in a notification) until one has room again.
    fn sync_crowded(&mut self) {
        let mut bars: Vec<isize> = self.mirrors.iter().map(|m| m.0.0 as isize).collect();
        if !self.primary_hidden {
            bars.push(self.taskbar.0 as isize);
        }
        let crowded = {
            let rooms = self.rooms.borrow();
            !bars.is_empty() && bars.iter().all(|b| rooms.get(b) == Some(&false))
        };
        if crowded == self.crowded {
            return;
        }
        self.crowded = crowded;
        dbg_log(&format!("not enough room on the taskbar: {crowded}"));
        if crowded {
            self.sync_tray();
            if self.crowded_said.is_none_or(|t| t.elapsed().as_secs() >= 600) {
                self.crowded_said = Some(Instant::now());
                self.notify_info(&tr("Not enough room on the taskbar"), &tr("The battery levels are shown as notification-area icons until there is room again. You can also move the widget: right-click it → Widget position."));
            }
        } else if !self.fallback {
            self.remove_tray();
        }
    }

    // ---- other monitors ("Show widget on") -----------------------------------------------------

    /// Keeps one copy of the strip on the taskbar of each extra monitor the user chose (left to
    /// right), next to that taskbar's clock. Taskbars of other monitors exist only when Windows
    /// shows the taskbar on all displays.
    fn sync_mirrors(&mut self) {
        if self.fallback || self.strip.0.is_null() {
            self.drop_mirrors();
            self.mirrors_ready = true;
            return;
        }
        let (bars, hide_primary) = self.chosen_bars();
        self.set_primary_hidden(hide_primary);
        // The notification bell or a longer date moves every taskbar's clock: check the Windows 11
        // secondary taskbars again when the main taskbar's notification area changes.
        if !bars.is_empty() {
            unsafe {
                if let Ok(tray) = FindWindowExW(Some(self.taskbar), None, w!("TrayNotifyWnd"), None) {
                    let mut tr = RECT::default();
                    let _ = GetWindowRect(tray, &mut tr);
                    if tr != self.main_tray {
                        self.main_tray = tr;
                        batteryhub::tray_probe::taskbars_changed();
                    }
                }
            }
        }
        // Drop copies whose taskbar is gone or no longer wanted.
        let all_bars = secondary_taskbars();
        let usable = |bar: HWND, strip: HWND| unsafe { IsWindow(Some(strip)).as_bool() && GetWindow(strip, GW_OWNER).is_ok_and(|p| p == bar) };
        let mut keep = Vec::new();
        for (bar, strip) in std::mem::take(&mut self.mirrors) {
            if bars.contains(&bar) && usable(bar, strip) {
                keep.push((bar, strip));
            } else if all_bars.contains(&bar) && usable(bar, strip) {
                // No longer wanted on that monitor: pops out, then waits hidden for its return.
                if unsafe { IsWindowVisible(strip).as_bool() } {
                    self.start_pop(strip, true);
                }
                self.parked.push((bar, strip));
            } else if is_our_strip(strip) {
                unsafe {
                    let _ = DestroyWindow(strip);
                }
            }
        }
        self.mirrors = keep;
        // Parked copies whose taskbar is gone go too.
        for (bar, strip) in std::mem::take(&mut self.parked) {
            if all_bars.contains(&bar) && usable(bar, strip) {
                self.parked.push((bar, strip));
            } else if is_our_strip(strip) {
                self.mirror_in.retain(|(h, _, _)| *h != strip);
                unsafe {
                    let _ = DestroyWindow(strip);
                }
            }
        }
        for bar in bars {
            if self.mirrors.iter().any(|m| m.0 == bar) {
                continue;
            }
            // A parked copy comes back (it pops in when place_mirror_at shows it).
            let strip = match self.parked.iter().position(|m| m.0 == bar) {
                Some(i) => self.parked.remove(i).1,
                None => {
                    let Some(strip) = create_copy(bar) else { continue };
                    dbg_log(&format!("mirror strip {strip:?} on {bar:?}"));
                    strip
                }
            };
            self.mirrors.push((bar, strip));
            self.push(strip);
        }
        // Every other taskbar gets a hidden copy ready, so the widget can appear there smoothly.
        for bar in all_bars {
            if self.mirrors.iter().any(|m| m.0 == bar) || self.parked.iter().any(|m| m.0 == bar) {
                continue;
            }
            if let Some(strip) = create_copy(bar) {
                dbg_log(&format!("parked strip {strip:?} on {bar:?}"));
                self.push(strip);
                self.parked.push((bar, strip));
            }
        }
        // Stray copies (e.g. left by an Explorer restart): our popups not in either list.
        {
            unsafe {
                let mut after: Option<HWND> = None;
                while let Ok(h) = FindWindowExW(None, after, STRIP_CLASS, None) {
                    if h.0.is_null() {
                        break;
                    }
                    after = Some(h);
                    if h != self.strip
                        && !self.mirrors.iter().any(|m| m.1 == h)
                        && !self.parked.iter().any(|m| m.1 == h)
                        && !self.popping(h)
                        && is_our_strip(h)
                    {
                        let _ = DestroyWindow(h);
                    }
                }
            }
        }
        let mut pending = false;
        for i in 0..self.mirrors.len() {
            pending |= self.place_mirror_at(i);
        }
        // The main strip waits for the copies, so all taskbars show the widget at the same moment.
        let was_ready = self.mirrors_ready;
        self.mirrors_ready = !pending;
        if self.mirrors_ready && !was_ready {
            self.last_place = Default::default();
            self.place();
        }
    }

    /// Taskbars of other monitors that show a copy of the widget, and whether the main taskbar's
    /// strip is hidden (the widget is shown only on one other monitor that is connected).
    fn chosen_bars(&self) -> (Vec<HWND>, bool) {
        let others = secondary_taskbars();
        match self.choice.as_str() {
            "all" => (others, false),
            "main" => (Vec::new(), false),
            id => {
                let ids: Vec<String> = others.iter().map(|b| monitor_id(*b)).collect();
                match find_monitor(&ids, id) {
                    Some(i) => (vec![others[i]], true),
                    None => (Vec::new(), false), // that monitor is not connected: main taskbar meanwhile
                }
            }
        }
    }

    /// Hides the main taskbar's strip while the widget is shown only on another monitor.
    fn set_primary_hidden(&mut self, hide: bool) {
        if self.strip.0.is_null() {
            self.primary_hidden = hide;
            return;
        }
        unsafe {
            if hide {
                if IsWindowVisible(self.strip).as_bool() && !self.primary_hidden {
                    // Leaving the main taskbar for another monitor: pops out, then hides.
                    self.start_pop(self.strip, true);
                } else if IsWindowVisible(self.strip).as_bool() && !self.popping(self.strip) {
                    let _ = ShowWindow(self.strip, SW_HIDE);
                }
                if !self.primary_hidden {
                    self.hide_tip();
                    // Windows 10 layout: give the task buttons their full width back.
                    if let (Ok(rebar), Ok(tray)) =
                        (FindWindowExW(Some(self.taskbar), None, w!("ReBarWindow32"), None), FindWindowExW(Some(self.taskbar), None, w!("TrayNotifyWnd"), None))
                    {
                        let (mut rr, mut tr) = (RECT::default(), RECT::default());
                        let _ = GetWindowRect(rebar, &mut rr);
                        let _ = GetWindowRect(tray, &mut tr);
                        let mut tl = POINT { x: rr.left, y: rr.top };
                        let mut tp = POINT { x: tr.left, y: tr.top };
                        let _ = ScreenToClient(self.taskbar, &mut tl);
                        let _ = ScreenToClient(self.taskbar, &mut tp);
                        if tp.x > tl.x {
                            let _ = MoveWindow(rebar, tl.x, tl.y, tp.x - tl.x, rr.bottom - rr.top, true);
                        }
                    }
                }
            } else if self.primary_hidden {
                self.last_place = Default::default();
                self.primary_hidden = false;
                let was = IsWindowVisible(self.strip).as_bool() && !self.popping(self.strip);
                self.place();
                if !was && IsWindowVisible(self.strip).as_bool() {
                    self.start_pop(self.strip, false);
                }
            }
        }
        self.primary_hidden = hide;
    }

    fn drop_mirrors(&mut self) {
        self.set_primary_hidden(false);
        self.mirror_in.retain(|(h, _, _)| *h == self.strip);
        let mut all = std::mem::take(&mut self.mirrors);
        all.append(&mut self.parked);
        for (_, strip) in all {
            if is_our_strip(strip) {
                unsafe {
                    let _ = DestroyWindow(strip);
                }
            }
        }
    }

    /// Places copy `i`; when that shows it (new, or hidden until now) it pops in with fresh content.
    fn place_mirror_at(&mut self, i: usize) -> bool {
        let (bar, strip) = self.mirrors[i];
        let was = unsafe { IsWindowVisible(strip).as_bool() };
        let pending = self.place_mirror(bar, strip);
        if !was && unsafe { IsWindowVisible(strip).as_bool() } {
            self.start_pop(strip, false);
        } else if !self.popping(strip) && unsafe { IsWindowVisible(strip).as_bool() } {
            // What a copy shows right after it appears can get lost on the way to the screen (it
            // stayed blank until the mouse went over it), so it gets its image again every tick.
            self.push(strip);
        }
        pending
    }

    /// A strip is popping in or out (its frames come from TIMER_MIRROR_IN).
    fn popping(&self, strip: HWND) -> bool {
        self.mirror_in.iter().any(|(h, _, _)| *h == strip)
    }

    /// Starts `strip` popping in, or out (`leaving`). A strip turning around part-way continues
    /// from where it is.
    fn start_pop(&mut self, strip: HWND, leaving: bool) {
        let now = Instant::now();
        let t0 = match self.mirror_in.iter().position(|(h, _, _)| *h == strip) {
            Some(i) => {
                let (_, t, was_leaving) = self.mirror_in.remove(i);
                let done = (t.elapsed().as_secs_f32() * 1000.0 / MIRROR_IN_MS).min(1.0);
                if was_leaving == leaving {
                    t
                } else {
                    now - std::time::Duration::from_secs_f32((1.0 - done) * MIRROR_IN_MS / 1000.0)
                }
            }
            None => now,
        };
        self.mirror_in.push((strip, t0, leaving));
        let p = (t0.elapsed().as_secs_f32() * 1000.0 / MIRROR_IN_MS).min(1.0);
        self.mirror_in_frame(strip, if leaving { 1.0 - p } else { p });
        unsafe {
            SetTimer(Some(self.main), TIMER_MIRROR_IN, 15, None);
        }
    }

    /// One frame of a copy popping in (`p` 0 to 1): it grows from 60 % around its centre with a
    /// small overshoot, fades in and is blurred while it moves, like the devices on the strip.
    fn mirror_in_frame(&self, strip: HWND, p: f32) {
        if p <= 0.0 {
            self.push_px(strip, &vec![0; self.pixels.len()]);
            return;
        }
        if p >= 1.0 {
            self.push(strip);
            return;
        }
        let (c1, c3) = (1.70158f32, 2.70158f32);
        let back = 1.0 + c3 * (p - 1.0).powi(3) + c1 * (p - 1.0).powi(2);
        let k = (0.6 + 0.4 * back).max(0.05);
        let blur = ((1.0 - p) * (1.0 - p) * 4.0 * self.scale()).round() as usize;
        let fade = p * p * (3.0 - 2.0 * p);
        let px = pop_pixels(&self.pixels, self.size.cx as usize, self.size.cy as usize, k, blur, fade);
        self.push_px(strip, &px);
    }

    /// TIMER_MIRROR_IN: advances the strips popping in or out; a copy that has popped out is
    /// destroyed, the main strip hidden. Stops when none is left.
    fn mirror_in_step(&mut self) {
        let list = std::mem::take(&mut self.mirror_in);
        for (strip, t0, leaving) in list {
            let p = (t0.elapsed().as_secs_f32() * 1000.0 / MIRROR_IN_MS).min(1.0);
            self.mirror_in_frame(strip, if leaving { 1.0 - p } else { p });
            if p < 1.0 {
                self.mirror_in.push((strip, t0, leaving));
            } else if leaving {
                unsafe {
                    if strip == self.strip || self.parked.iter().any(|m| m.1 == strip) {
                        let _ = ShowWindow(strip, SW_HIDE);
                        self.push(strip); // full content again for its next appearance
                    } else if is_our_strip(strip) && !self.mirrors.iter().any(|m| m.1 == strip) {
                        let _ = DestroyWindow(strip);
                    }
                }
            }
        }
        if self.mirror_in.is_empty() {
            unsafe {
                let _ = KillTimer(Some(self.main), TIMER_MIRROR_IN);
            }
        }
    }

    /// Places a copy just left of the secondary taskbar's clock (Windows 10 / ExplorerPatcher
    /// layout), or, when there is no clock window (Windows 11 draws it itself), just left of the
    /// first notification-area item that UI Automation reports (see tray_probe).
    /// Returns true while the copy is hidden because its place is not known yet.
    fn place_mirror(&self, bar: HWND, strip: HWND) -> bool {
        unsafe {
            // A copy is a topmost window of its own: it must not stay over a full-screen game or
            // video on that monitor (the taskbar itself goes behind those).
            if fullscreen_over(bar) {
                if IsWindowVisible(strip).as_bool() {
                    let _ = ShowWindow(strip, SW_HIDE);
                }
                return false;
            }
            let mut br = RECT::default();
            let _ = GetWindowRect(bar, &mut br);
            let dpi = GetDpiForWindow(bar);
            let s = if dpi == 0 { 1.0 } else { dpi as f32 / 96.0 };
            if br.bottom - br.top > br.right - br.left {
                // A vertical taskbar (left / right): like the main one, just above its clock and
                // centred across its width. The copy is drawn in the main taskbar's layout, so a
                // vertical copy only fits when the main taskbar is vertical too.
                if !self.vertical {
                    let _ = ShowWindow(strip, SW_HIDE);
                    return false;
                }
                dbg_log(&format!("mirror: vertical bar {bar:?} rect {},{},{},{} main vertical {}", br.left, br.top, br.right, br.bottom, self.vertical));
                let bottom = match FindWindowExW(Some(bar), None, w!("ClockButton"), None) {
                    Ok(clock) if !clock.0.is_null() && IsWindowVisible(clock).as_bool() => {
                        let mut cr = RECT::default();
                        let _ = GetWindowRect(clock, &mut cr);
                        cr.top
                    }
                    // Windows 11 (with a vertical-taskbar mod) draws the clock itself: ask UI
                    // Automation where its notification-area items start, as for horizontal ones.
                    _ => match batteryhub::tray_probe::tray_left(bar, br, self.main, WM_TRAY_PROBED) {
                        batteryhub::tray_probe::TrayEdge::Known(y) => y,
                        batteryhub::tray_probe::TrayEdge::Pending => return true,
                        batteryhub::tray_probe::TrayEdge::Unknown => br.bottom - (130.0 * s) as i32,
                    },
                };
                let mut p = POINT { x: br.left, y: bottom };
                let _ = ScreenToClient(bar, &mut p);
                let mut top = p.y - self.size.cy - (2.0 * s) as i32;
                if self.offset > 0 {
                    top -= (self.offset as f32 * s) as i32;
                }
                let mut client = RECT::default();
                let _ = GetClientRect(bar, &mut client);
                let left = ((client.right - self.size.cx) / 2).max(0);
                self.rooms.borrow_mut().remove(&(bar.0 as isize));
                self.show_mirror_at(bar, strip, left, top.max(0), self.size);
                return false;
            }
            let right = match FindWindowExW(Some(bar), None, w!("ClockButton"), None) {
                Ok(clock) if !clock.0.is_null() && IsWindowVisible(clock).as_bool() => {
                    let mut cr = RECT::default();
                    let _ = GetWindowRect(clock, &mut cr);
                    cr.left
                }
                // Windows 11 draws this taskbar's clock itself: ask UI Automation where its
                // notification-area items start (cached; an estimate until the first answer).
                _ => match batteryhub::tray_probe::tray_left(bar, br, self.main, WM_TRAY_PROBED) {
                    batteryhub::tray_probe::TrayEdge::Known(x) => x,
                    // Not known yet (well under a second): stay hidden rather than show the copy in
                    // the wrong place; WM_TRAY_PROBED places it as soon as the answer is there.
                    batteryhub::tray_probe::TrayEdge::Pending => return true,
                    batteryhub::tray_probe::TrayEdge::Unknown => br.right - (130.0 * s) as i32,
                },
            };
            let left = if self.align_left {
                let found = if self.after_icons {
                    let exclude = screen_spans(bar, &foreign_widgets(bar));
                    batteryhub::tray_probe::icons_end(bar, br, right, &exclude, self.main, WM_TRAY_PROBED)
                } else {
                    batteryhub::tray_probe::left_content_end(bar, br, self.main, WM_TRAY_PROBED)
                };
                let Some(x) = found else { return true };
                let mut p = POINT { x, y: br.top };
                let _ = ScreenToClient(bar, &mut p);
                p.x + (6.0 * s) as i32
            } else {
                let mut p = POINT { x: right, y: br.top };
                let _ = ScreenToClient(bar, &mut p);
                let mut left = p.x - self.size.cx - (2.0 * s) as i32;
                if self.offset > 0 {
                    left -= (self.offset as f32 * s) as i32;
                }
                avoid_widgets(bar, left, self.size.cx, (4.0 * s) as i32)
            };
            let mut client = RECT::default();
            let _ = GetClientRect(bar, &mut client);
            let top = ((client.bottom - self.size.cy) / 2).max(0);
            // Narrow the task buttons so they never slide under the copy.
            if let Ok(worker) = FindWindowExW(Some(bar), None, w!("WorkerW"), None) {
                let mut wr = RECT::default();
                let _ = GetWindowRect(worker, &mut wr);
                let mut tl = POINT { x: wr.left, y: wr.top };
                let _ = ScreenToClient(bar, &mut tl);
                if tl.x + (wr.right - wr.left) > left && left > tl.x {
                    let _ = MoveWindow(worker, tl.x, tl.y, left - tl.x, wr.bottom - wr.top, true);
                }
            }
            // Not enough room beside this taskbar's task buttons: hidden there (see tick).
            let mut x0 = POINT { x: left, y: top };
            let _ = ClientToScreen(bar, &mut x0);
            let age = if self.align_left { ROOM_LEFT_AGE } else { ROOM_AGE };
            let room = batteryhub::tray_probe::room(bar, br, x0.x, x0.x + self.size.cx, self.main, WM_TRAY_PROBED, age, IsWindowVisible(strip).as_bool()).is_none_or(|r| r)
                && x0.x + self.size.cx <= right;
            self.rooms.borrow_mut().insert(bar.0 as isize, room);
            if !room {
                self.mirror_glides.borrow_mut().retain(|g| g.0 != strip);
                if IsWindowVisible(strip).as_bool() {
                    let _ = ShowWindow(strip, SW_HIDE);
                }
                return false;
            }
            self.show_mirror_at(bar, strip, left, top, self.size);
        }
        false
    }

    /// Moves a copy to `left`, `top` (client coordinates of its taskbar) unless it is already there.
    /// Moving or resizing a layered child window can drop what it shows until its next update
    /// (it stayed blank until the mouse went over it), so it gets its image again after a move.
    fn show_mirror_at(&self, bar: HWND, strip: HWND, left: i32, top: i32, size: SIZE) {
        unsafe {
            let mut cur = RECT::default();
            let _ = GetWindowRect(strip, &mut cur);
            let mut cp = POINT { x: cur.left, y: cur.top };
            let _ = ScreenToClient(bar, &mut cp);
            let hidden = !IsWindowVisible(strip).as_bool();
            let same = cp.x == left && cp.y == top && cur.right - cur.left == size.cx && cur.bottom - cur.top == size.cy;
            if hidden || !same {
                // A popup: screen coordinates, above the (topmost) taskbar.
                let mut sp = POINT { x: left, y: top };
                let _ = ClientToScreen(bar, &mut sp);
                // Shown, same size, only a new place: it glides there (glide_step), like the main strip.
                let same_size = cur.right - cur.left == size.cx && cur.bottom - cur.top == size.cy;
                let mut glides = self.mirror_glides.borrow_mut();
                if !hidden && same_size && !self.popping(strip) {
                    let from = POINT { x: cur.left, y: cur.top };
                    match glides.iter_mut().find(|g| g.0 == strip) {
                        Some(g) if g.2 == sp => {}
                        Some(g) => *g = (strip, from, sp, Instant::now()),
                        None => glides.push((strip, from, sp, Instant::now())),
                    }
                    SetTimer(Some(self.main), TIMER_GLIDE, 15, None);
                    return;
                }
                glides.retain(|g| g.0 != strip);
                drop(glides);
                if self.popping(strip) {
                    let _ = SetWindowPos(strip, Some(HWND_TOPMOST), sp.x, sp.y, size.cx, size.cy, SWP_NOACTIVATE | SWP_SHOWWINDOW);
                } else {
                    // New image, size and place in one step, then shown (on top) if it was hidden.
                    let px = if strip == self.hovered && self.lit.len() == self.pixels.len() { &self.lit } else { &self.pixels };
                    self.push_px_at(strip, px, Some(sp));
                    if hidden {
                        let _ = SetWindowPos(strip, Some(HWND_TOPMOST), 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE | SWP_SHOWWINDOW);
                    }
                }
            }
        }
    }

    // ---- notification-area fallback ------------------------------------------------------------

    fn tray_data(&self, uid: u32) -> NOTIFYICONDATAW {
        NOTIFYICONDATAW { cbSize: size_of::<NOTIFYICONDATAW>() as u32, hWnd: self.main, uID: uid, ..Default::default() }
    }

    /// One icon per device with its level drawn in it; the tooltip is the same as on the strip.
    fn sync_tray(&mut self) {
        let light = self.light;
        let normal = if light { rgb(20, 20, 20) } else { rgb(255, 255, 255) };
        let size = unsafe { windows::Win32::UI::HiDpi::GetSystemMetricsForDpi(SM_CXSMICON, windows::Win32::UI::HiDpi::GetDpiForSystem()) };
        let devices = self.visible();
        // Opt-in for this prototype; ordinary installations retain the original icons.
        let stacked = std::env::var_os("BATTERYHUB_TRAY_DEVICE_GLYPHS").as_deref() == Some(std::ffi::OsStr::new("1"));
        let mut wanted: Vec<TrayIcon> = devices
            .iter()
            .enumerate()
            .map(|(i, d)| {
                let th = settings::threshold(SETTINGS_KEY, &d.key);
                let text = if d.percent >= 0 { d.percent.to_string() } else { "?".into() };
                (d.key.clone(), text, ui::level_color(d, light, normal, th), d.percent, self.tip_text(i), stacked.then(|| d.kind.glyph()))
            })
            .collect();
        if wanted.is_empty() {
            wanted.push(("\u{0}none".into(), "-".into(), normal, -1, tr("BatteryHub: no devices found"), None));
        }
        let keep: HashSet<String> = wanted.iter().map(|w| w.0.clone()).collect();
        let stale: Vec<String> = self.tray.keys().filter(|k| !keep.contains(*k)).cloned().collect();
        for k in stale {
            self.remove_tray_icon(&k);
        }
        for (key, text, color, level, tip, glyph) in wanted {
            let rendered = match glyph {
                Some(g) => ui::device_number_icon(&text, color, level, size, light, g),
                None => ui::number_icon(&text, color, level, size, light),
            };
            let Some(icon) = rendered else {
                continue;
            };
            // The id comes from the device key, so a device keeps its icon id across restarts and
            // Windows remembers per device whether it is shown on the taskbar or hidden.
            let uid = match self.tray.get(&key) {
                Some((u, _)) => *u,
                None => tray_uid(&key, self.tray.values().map(|v| v.0).collect()),
            };
            let mut d = self.tray_data(uid);
            d.uFlags = NIF_ICON | NIF_TIP | NIF_MESSAGE | NIF_SHOWTIP;
            d.uCallbackMessage = WM_TRAY;
            d.hIcon = icon;
            ui::fill_wide(&mut d.szTip, &tip);
            unsafe {
                let known = self.tray.contains_key(&key);
                if !known || !Shell_NotifyIconW(NIM_MODIFY, &d).as_bool() {
                    let _ = Shell_NotifyIconW(NIM_ADD, &d);
                }
            }
            if let Some((_, old)) = self.tray.insert(key, (uid, icon)) {
                unsafe {
                    let _ = DestroyIcon(old);
                }
            }
        }
    }

    fn remove_tray_icon(&mut self, key: &str) {
        if let Some((uid, icon)) = self.tray.remove(key) {
            unsafe {
                let _ = Shell_NotifyIconW(NIM_DELETE, &self.tray_data(uid));
                let _ = DestroyIcon(icon);
            }
        }
    }

    /// The app's own notification-area icon: shown while the strip has nothing to show because the
    /// empty-strip icon is turned off, so the menu stays a right-click away.
    fn sync_app_icon(&mut self) {
        let want = self.hide_empty && self.loaded && !self.fallback && self.visible().is_empty();
        unsafe {
            match (want, self.app_icon) {
                (true, None) => {
                    let size = windows::Win32::UI::HiDpi::GetSystemMetricsForDpi(SM_CXSMICON, windows::Win32::UI::HiDpi::GetDpiForSystem());
                    let hinst = GetModuleHandleW(None).unwrap_or_default();
                    let Ok(h) = LoadImageW(Some(hinst.into()), windows::core::PCWSTR(1 as _), IMAGE_ICON, size, size, LR_DEFAULTCOLOR) else { return };
                    let icon = HICON(h.0);
                    let mut d = self.tray_data(APP_UID);
                    d.uFlags = NIF_ICON | NIF_TIP | NIF_MESSAGE | NIF_SHOWTIP;
                    d.uCallbackMessage = WM_TRAY;
                    d.hIcon = icon;
                    ui::fill_wide(&mut d.szTip, &tr("BatteryHub: no devices found"));
                    if !Shell_NotifyIconW(NIM_MODIFY, &d).as_bool() {
                        let _ = Shell_NotifyIconW(NIM_ADD, &d);
                    }
                    self.app_icon = Some(icon);
                }
                (false, Some(icon)) => {
                    let _ = Shell_NotifyIconW(NIM_DELETE, &self.tray_data(APP_UID));
                    let _ = DestroyIcon(icon);
                    self.app_icon = None;
                }
                _ => {}
            }
        }
    }

    fn remove_tray(&mut self) {
        let keys: Vec<String> = self.tray.keys().cloned().collect();
        for k in keys {
            self.remove_tray_icon(&k);
        }
    }

    /// Keeps the strip just left of the notification area (checked every second, like the original).
    fn place(&mut self) {
        if self.strip.0.is_null() || self.primary_hidden || !self.mirrors_ready {
            return;
        }
        unsafe {
            if self.strip_popup && (fullscreen_over(self.taskbar) || !IsWindowVisible(self.taskbar).as_bool()) {
                if IsWindowVisible(self.strip).as_bool() {
                    let _ = ShowWindow(self.strip, SW_HIDE);
                }
                return;
            }
            let Ok(tray) = FindWindowExW(Some(self.taskbar), None, w!("TrayNotifyWnd"), None) else {
                return;
            };
            let (mut tr, mut bar) = (RECT::default(), RECT::default());
            let _ = GetWindowRect(tray, &mut tr);
            let _ = GetWindowRect(self.taskbar, &mut bar);
            if self.vertical {
                // Above the notification area, centred across the taskbar's width.
                let mut p = POINT { x: bar.left, y: tr.top };
                let _ = ScreenToClient(self.taskbar, &mut p);
                let mut client = RECT::default();
                let _ = GetClientRect(self.taskbar, &mut client);
                let mut top = p.y - self.size.cy - (2.0 * self.scale()) as i32;
                if self.offset > 0 {
                    top -= (self.offset as f32 * self.scale()) as i32;
                }
                let top = top.max(0);
                let left = ((client.right - self.size.cx) / 2).max(0);
                self.rooms.borrow_mut().remove(&(self.taskbar.0 as isize));
                self.place_strip_at(left, top, (tr, bar, top));
                return;
            }
            let left = if self.align_left {
                // Next to the taskbar icons (or the left end, after the widgets button, when they are
                // centred); placed as soon as UI Automation has told where they end.
                let found = if self.after_icons {
                    let exclude = screen_spans(self.taskbar, &foreign_widgets(self.taskbar));
                    batteryhub::tray_probe::icons_end(self.taskbar, bar, tr.left, &exclude, self.main, WM_TRAY_PROBED)
                } else {
                    batteryhub::tray_probe::left_content_end(self.taskbar, bar, self.main, WM_TRAY_PROBED)
                };
                let Some(x) = found else { return };
                let mut p = POINT { x, y: bar.top };
                let _ = ScreenToClient(self.taskbar, &mut p);
                p.x + (6.0 * self.scale()) as i32
            } else {
                let mut p = POINT { x: tr.left, y: bar.top };
                let _ = ScreenToClient(self.taskbar, &mut p);
                let mut left = p.x - self.size.cx - (2.0 * self.scale()) as i32;
                // Optional extra gap (DPI-independent px), e.g. to sit next to another taskbar widget.
                if self.offset > 0 {
                    left -= (self.offset as f32 * self.scale()) as i32;
                }
                // Other programs' widgets in the taskbar: sit left of them instead of on top.
                avoid_widgets(self.taskbar, left, self.size.cx, (4.0 * self.scale()) as i32)
            };
            let mut client = RECT::default();
            let _ = GetClientRect(self.taskbar, &mut client);
            let top = ((client.bottom - self.size.cy) / 2).max(0);

            // Windows 10 / ExplorerPatcher taskbar: narrow the task buttons so they never slide under us.
            if let Ok(rebar) = FindWindowExW(Some(self.taskbar), None, w!("ReBarWindow32"), None).map_err(|_| ()).and_then(|r| if self.align_left { Err(()) } else { Ok(r) }) {
                let mut rr = RECT::default();
                let _ = GetWindowRect(rebar, &mut rr);
                let mut tl = POINT { x: rr.left, y: rr.top };
                let _ = ScreenToClient(self.taskbar, &mut tl);
                if tl.x + (rr.right - rr.left) > left && left > tl.x {
                    let _ = MoveWindow(rebar, tl.x, tl.y, left - tl.x, rr.bottom - rr.top, true);
                }
            }
            // Not enough room beside the task buttons: hidden on this taskbar (see tick).
            let mut x0 = POINT { x: left, y: top };
            let _ = ClientToScreen(self.taskbar, &mut x0);
            let age = if self.align_left { ROOM_LEFT_AGE } else { ROOM_AGE };
            let room = batteryhub::tray_probe::room(self.taskbar, bar, x0.x, x0.x + self.size.cx, self.main, WM_TRAY_PROBED, age, IsWindowVisible(self.strip).as_bool()).is_none_or(|r| r)
                && x0.x + self.size.cx <= tr.left;
            self.rooms.borrow_mut().insert(self.taskbar.0 as isize, room);
            if !room {
                self.glide = None;
                self.last_place = Default::default();
                if IsWindowVisible(self.strip).as_bool() {
                    self.hide_tip();
                    let _ = ShowWindow(self.strip, SW_HIDE);
                }
                return;
            }
            self.place_strip_at(left, top, (tr, bar, left));
        }
    }

    fn place_strip_at(&mut self, left: i32, top: i32, key: (RECT, RECT, i32)) {
        unsafe {
            if self.strip_popup {
                let mut sp = POINT { x: left, y: top };
                let _ = ClientToScreen(self.taskbar, &mut sp);
                let hidden = !IsWindowVisible(self.strip).as_bool();
                let mut cur = RECT::default();
                let _ = GetWindowRect(self.strip, &mut cur);
                let moved = cur.left != sp.x || cur.top != sp.y || cur.right - cur.left != self.size.cx || cur.bottom - cur.top != self.size.cy;
                if !hidden && !moved && self.last_place == key {
                    return;
                }
                self.last_place = key;
                if self.popping(self.strip) {
                    let _ = SetWindowPos(self.strip, Some(HWND_TOPMOST), sp.x, sp.y, self.size.cx, self.size.cy, SWP_NOACTIVATE | SWP_SHOWWINDOW);
                } else {
                    let px = if self.strip == self.hovered && self.lit.len() == self.pixels.len() { &self.lit } else { &self.pixels };
                    self.push_px_at(self.strip, px, Some(sp));
                    if hidden {
                        let _ = SetWindowPos(self.strip, Some(HWND_TOPMOST), 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE | SWP_SHOWWINDOW);
                    }
                }
                return;
            }
            let covered = GetWindow(self.strip, GW_HWNDPREV).is_ok_and(|h| !h.0.is_null()) || !IsWindowVisible(self.strip).as_bool();
            if !covered && self.last_place == key {
                return;
            }
            self.last_place = key;
            self.move_strip(left, top);
        }
    }

    /// Puts the strip at `left`, `top` (taskbar client coordinates), on top of the taskbar's own
    /// windows. A visible strip of the same size glides there (from where it is, also part-way
    /// through a glide) instead of jumping; a new size or a hidden strip is placed right away.
    fn move_strip(&mut self, left: i32, top: i32) {
        let to = POINT { x: left, y: top };
        unsafe {
            let mut cur = RECT::default();
            let _ = GetWindowRect(self.strip, &mut cur);
            let mut from = POINT { x: cur.left, y: cur.top };
            let _ = ScreenToClient(self.taskbar, &mut from);
            let same_size = cur.right - cur.left == self.size.cx && cur.bottom - cur.top == self.size.cy;
            let visible = IsWindowVisible(self.strip).as_bool();
            let raise = SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE | SWP_SHOWWINDOW;
            if visible && same_size && self.glide.is_some_and(|g| g.1 == to) {
                let _ = SetWindowPos(self.strip, Some(HWND_TOP), 0, 0, 0, 0, raise);
                return;
            }
            if visible && same_size && from != to {
                self.glide = Some((from, to, Instant::now()));
                let _ = SetWindowPos(self.strip, Some(HWND_TOP), 0, 0, 0, 0, raise);
                SetTimer(Some(self.main), TIMER_GLIDE, 15, None);
                return;
            }
            self.glide = None;
            let _ = SetWindowPos(self.strip, Some(HWND_TOP), left, top, self.size.cx, self.size.cy, SWP_NOACTIVATE | SWP_SHOWWINDOW);
        }
    }

    /// The height shift drawn now (px before scaling): offset_y, or on its way there.
    fn shown_offset_y(&self) -> f32 {
        match self.y_glide {
            Some((from, t0)) => from + (self.offset_y as f32 - from) * glide_ease(t0),
            None => self.offset_y as f32,
        }
    }

    /// TIMER_GLIDE: one frame of the strip moving and / or its height shift changing.
    fn glide_step(&mut self) {
        if let Some((from, to, t0)) = self.glide {
            let e = glide_ease(t0);
            let x = from.x + ((to.x - from.x) as f32 * e).round() as i32;
            let y = from.y + ((to.y - from.y) as f32 * e).round() as i32;
            unsafe {
                let _ = SetWindowPos(self.strip, None, x, y, 0, 0, SWP_NOSIZE | SWP_NOZORDER | SWP_NOACTIVATE);
            }
            if e >= 1.0 {
                self.glide = None;
            }
        }
        let glides = std::mem::take(&mut *self.mirror_glides.borrow_mut());
        let mut going = Vec::new();
        for (strip, from, to, t0) in glides {
            if !self.mirrors.iter().any(|m| m.1 == strip) || unsafe { !IsWindowVisible(strip).as_bool() } {
                continue;
            }
            let e = glide_ease(t0);
            let at = POINT { x: from.x + ((to.x - from.x) as f32 * e).round() as i32, y: from.y + ((to.y - from.y) as f32 * e).round() as i32 };
            let px = if strip == self.hovered && self.lit.len() == self.pixels.len() { &self.lit } else { &self.pixels };
            self.push_px_at(strip, px, Some(at));
            if e < 1.0 {
                going.push((strip, from, to, t0));
            }
        }
        self.mirror_glides.borrow_mut().extend(going);
        if let Some((_, t0)) = self.y_glide {
            if glide_ease(t0) >= 1.0 {
                self.y_glide = None;
            }
            self.paint();
        }
        if self.glide.is_none() && self.y_glide.is_none() && self.mirror_glides.borrow().is_empty() {
            unsafe {
                let _ = KillTimer(Some(self.main), TIMER_GLIDE);
            }
        }
    }

    // ---- hover card ----------------------------------------------------------------------------

    /// Records the levels of this read in the 7-day history (one point per change of level or
    /// charging state, or every 10 minutes), drops what is older than 7 days, and saves it on a
    /// worker thread at most every 10 minutes (right away while a dashboard shows it).
    fn record_history(&mut self, fresh: &[DeviceStatus]) {
        let now = batteryhub::history::now_secs();
        let gap = batteryhub::history::gap_limit(refresh_minutes());
        for s in fresh {
            if s.connected && !s.asleep && s.percent >= 0 && !s.key.starts_with("demo:") && !settings::battery_only(SETTINGS_KEY, &s.key) {
                self.history.record(&s.key, now, s.percent, s.charging, s.is_full(), gap);
                if let Some(b) = s.buds {
                    for (side, level, charging) in [("L", b.left, b.left_charging), ("R", b.right, b.right_charging)] {
                        if level >= 0 {
                            self.history.record(&format!("{}#{side}", s.key), now, level, charging, false, gap);
                        }
                    }
                }
            }
        }
        self.history.prune(now);
        let live = dashboard_open();
        if live {
            // The dashboard reads the file: give it the latest reading too.
            self.history.flush();
        }
        let due = self.history_saved.is_none_or(|t| t.elapsed().as_secs() >= batteryhub::history::STEP_SECS);
        if self.history.is_dirty() && (due || live) {
            let main = self.main.0 as usize;
            let started = self.history.save_in_background(history_path(), move |ok| unsafe {
                let _ = PostMessageW(Some(HWND(main as *mut c_void)), WM_HISTORY_SAVED, WPARAM(ok as usize), LPARAM(0));
            });
            if started {
                self.history_saved = Some(Instant::now());
            }
        }
    }

    /// Stores what is kept in memory and writes the history now (exit, sign-out, sleep).
    fn save_history_now(&mut self) {
        self.history.flush();
        if self.history.is_dirty() {
            let _ = self.history.save_to(&history_path());
        }
    }

    /// Card colours: background, border.
    fn card_colors(&self) -> (COLORREF, COLORREF) {
        if self.light { (rgb(249, 249, 249), rgb(214, 214, 214)) } else { (rgb(44, 44, 44), rgb(70, 70, 70)) }
    }

    /// What the card of `d` shows: when this changes, the card is drawn again. The minute is part
    /// of it, so the chart's time axis moves on while the mouse rests on a device.
    fn card_signature(&self, d: &DeviceStatus) -> u64 {
        let h = self.history.points(&d.key);
        let last = self.history.latest(&d.key).map(|p| (p.t, p.level, p.flags));
        let text = format!(
            "{:?}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{:?}|{:?}|{}|{:?}|{:?}|{:?}|{:?}",
            card_opts(&d.key),
            d.key,
            d.name,
            d.percent,
            d.level_text,
            d.charging,
            d.full,
            d.asleep,
            d.via,
            self.light,
            self.scale().to_bits(),
            last,
            h.len(),
            batteryhub::history::now_secs() / 60,
            self.card_scrub.as_ref().filter(|(k, _)| *k == d.key).map(|(_, t)| t),
            d.buds,
            d.dock_percent,
            // The buds' own charts.
            ["#L", "#R"].map(|side| self.history.latest(&format!("{}{side}", d.key)).map(|p| (p.t, p.level, p.flags)))
        );
        batteryhub::util::fnv1a(&text) as u64
    }

    /// The card's content for `d`: from the cache when nothing changed, else drawn again.
    fn card_content(&mut self, d: &DeviceStatus) -> Rc<CardContent> {
        let sig = self.card_signature(d);
        if let Some(c) = self.card_cache.iter().find(|c| c.key == d.key && c.sig == sig) {
            return c.clone();
        }
        let t0 = Instant::now();
        let (w, h, px) = self.render_card(d);
        prof::add(&prof::RENDERS, 1);
        prof::add(&prof::RENDER_US, t0.elapsed().as_micros() as u64);
        let c = Rc::new(CardContent { sig, key: d.key.clone(), w, h, px, half: std::cell::OnceCell::new() });
        self.card_cache.retain(|o| o.key != d.key);
        self.card_cache.insert(0, c.clone());
        self.card_cache.truncate(2);
        c
    }

    /// Draws the content of the card for one device (name, level, bar, connection, last 24
    /// hours) on a transparent canvas; the rounded background is drawn per frame, so it can
    /// glide and stretch from one device's card to the next.
    fn render_card(&mut self, d: &DeviceStatus) -> (i32, i32, Vec<u32>) {
        self.ensure_fonts();
        let s = self.scale();
        let px = |v: f32| (v * s).round() as i32;
        let light = self.light;
        let fg = if light { rgb(0, 0, 0) } else { rgb(255, 255, 255) };
        let dim = if light { rgb(96, 96, 96) } else { rgb(170, 170, 170) };
        let track = if light { rgb(214, 214, 214) } else { rgb(80, 80, 80) };
        let grid = if light { rgb(200, 200, 200) } else { rgb(84, 84, 84) };
        let th = settings::threshold(SETTINGS_KEY, &d.key);
        let low = d.percent >= 0 && d.percent <= th && !d.charging;
        let accent = if low {
            ui::low_color(light)
        } else if light {
            rgb(16, 124, 16)
        } else {
            rgb(108, 203, 95)
        };
        let charge_c = if light { rgb(0, 95, 184) } else { rgb(96, 205, 255) };
        // The chart: green above the red-warning level, red at or below it (charging stays blue).
        let (ok_c, low_c) = (if light { rgb(16, 124, 16) } else { rgb(108, 203, 95) }, ui::low_color(light));
        let level_c = move |level: f64, charging: bool| {
            if charging {
                charge_c
            } else if level <= th as f64 {
                low_c
            } else {
                ok_c
            }
        };
        let Some(f) = self.fonts.as_ref() else { return (1, 1, vec![0]) };
        let (icon_f, name_f, big_f, small_f) = (f.card_icon, f.card_name, f.card_big, f.card_small);

        // As wide as the name needs, 300 to 400 px; longer names end in "…". Earbuds show their
        // case's level after the name, when they report it (the buds' levels are the big text).
        let pad = px(16.0);
        let buds = d
            .buds
            .filter(|_| d.connected && !d.asleep)
            .and_then(|b| b.case)
            .map(|(level, chg)| mask(&format!("{}{}", trf("Case {level}", &[("level", &format!("{level}%"))]), if chg { "⚡" } else { "" }), small_f, light));
        let buds_w = buds.as_ref().map_or(0, |m| m.w + px(10.0));
        let room = px(400.0) - 2 * pad - px(26.0) - buds_w;
        let mut name_text = d.name.clone();
        let mut name = mask(&name_text, name_f, light);
        let mut chars: Vec<char> = d.name.chars().collect();
        while name.w > room && chars.len() > 4 {
            chars.pop();
            name_text = format!("{}…", chars.iter().collect::<String>().trim_end());
            name = mask(&name_text, name_f, light);
        }
        let w = (name.w + buds_w + 2 * pad + px(26.0)).clamp(px(300.0), px(400.0));
        let chart_h = px(80.0);
        // Drawn on a tall canvas, then cut to the content's height plus the bottom margin.
        let tall = px(420.0);
        let mut cv = Canvas { w, h: tall, px: vec![0; (w * tall) as usize] };

        // Header: device glyph and name.
        let mut y = pad;
        let glyph = device_icon(d, icon_f, light);
        cv.draw(&glyph, pad, y + px(2.0), fg, 255);
        cv.draw(&name, pad + px(26.0), y, fg, 255);
        if let Some(b) = &buds {
            cv.draw(b, pad + px(26.0) + name.w + px(10.0), y + (name.h - b.h) / 2 + px(1.0), dim, 255);
        }
        y += px(34.0);

        // Big level (or the device's own word for it), the time left under it, then the bar.
        let big_text = if let Some(b) = d.buds.filter(|b| d.percent >= 0 && b.left >= 0 && b.right >= 0) {
            // Earbuds: each bud, labelled.
            format!("{}: {}%  {}: {}%", tr("L"), b.left, tr("R"), b.right)
        } else if d.percent >= 0 {
            format!("{}%", d.percent)
        } else if !d.level_text.is_empty() {
            d.level_text.clone()
        } else {
            "?".into()
        };
        let big = mask(&big_text, big_f, light);
        // Too long for the card at the big size (both buds): the name's size, on the same line.
        let (big, dy) = if big.w > w - 2 * pad {
            let small = mask(&big_text, name_f, light);
            let dy = (big.h - small.h) / 2;
            (small, dy)
        } else {
            (big, 0)
        };
        cv.draw(&big, pad, y + dy, if low { accent } else { fg }, 255);
        y += px(40.0);
        let now = batteryhub::history::now_secs();
        let series = self.history.series(&d.key);
        let read_now = d.connected && !d.asleep && d.percent >= 0;
        let st = batteryhub::stats::compute(&series, read_now.then_some((d.percent, d.charging)));
        // Rate of the forecast: down on battery, up while charging (none when full or not read).
        let est = if !read_now || d.is_full() {
            None
        } else if d.charging {
            st.charge_estimate()
        } else {
            st.discharge_estimate()
        };
        let (show_chart, show_time) = card_opts(&d.key);
        let left_text = if !read_now || d.is_full() || !show_time {
            String::new()
        } else {
            match st.time_left(d.percent, d.charging) {
                Some((h, _)) if d.charging => trf("full in about {time}", &[("time", &fmt_hours(h))]),
                Some((h, _)) => trf("about {time} left", &[("time", &fmt_hours(h))]),
                None => tr("Time left: not enough data yet"),
            }
        };
        if !left_text.is_empty() {
            let left = mask(&left_text, small_f, light);
            cv.draw(&left, pad, y, if est.is_some() { fg } else { dim }, 255);
        }
        if show_time {
            y += px(22.0); // same layout for every device, so cards share one height
        } else {
            y -= px(4.0); // no time-left line: the bar moves up under the level
        }
        cv.fill_rrect(pad, y, w - pad, y + px(6.0), px(3.0), track, 255);
        if d.percent > 0 {
            let fill = pad + (w - 2 * pad) * d.percent.min(100) / 100;
            cv.fill_rrect(pad, y, fill.max(pad + px(6.0)), y + px(6.0), px(3.0), accent, 255);
        }
        y += px(18.0);

        // Connection and state.
        let mut line = tr(&d.via);
        if d.charging {
            line.push_str(&format!(" · {}", if d.full { tr("Full") } else { tr("Charging") }));
        } else if d.asleep {
            line.push_str(&format!(" · {}", tr("Asleep")));
        }
        let via = mask(&line, small_f, light);
        cv.draw(&via, pad, y, dim, 255);
        // The spare battery in the headset's dock, when there is one.
        if let Some(dock) = d.dock_text() {
            y += px(20.0);
            cv.draw(&mask(&trf("Dock battery: {dock}", &[("dock", &dock)]), small_f, light), pad, y, dim, 255);
        }
        if !show_chart {
            // No chart: the card ends under the connection line.
            self.card_chart_y = (i32::MIN / 2, i32::MIN / 2);
            let h = (y + px(18.0) + pad).min(tall);
            cv.px.truncate((w * h) as usize);
            return (w, h, cv.px);
        }
        y += px(30.0);

        // The last 12 hours, now in the middle, and the next 12 hours as a forecast at the current
        // rate. Earbuds get one chart per bud, the left one over the right one. With the mouse on
        // the chart, the hour under it (level and change) replaces the title.
        let (from, to) = (now.saturating_sub(12 * 3600), now + 12 * 3600);
        let title_y = y;
        y += px(22.0);
        // (history key, side label, level now, charging now)
        let lanes: Vec<(String, Option<String>, i32, bool)> = match d.buds.filter(|_| d.connected) {
            Some(b) => vec![
                (format!("{}#L", d.key), Some(tr("L")), if read_now { b.left } else { -1 }, b.left_charging),
                (format!("{}#R", d.key), Some(tr("R")), if read_now { b.right } else { -1 }, b.right_charging),
            ],
            None => vec![(d.key.clone(), None, if read_now { d.percent } else { -1 }, d.charging)],
        };
        let lane_h = if lanes.len() > 1 { px(56.0) } else { chart_h };
        let lane_gap = px(12.0);
        let (x0, x1) = (pad, w - pad);
        let lw = px(2.0).max(2);
        let to_x = |t: u64| x0 + ((x1 - x0) as f32 * (t.saturating_sub(from) as f32 / (to - from) as f32).min(1.0)) as i32;
        let xm = to_x(now);
        let scrub = self.card_scrub.as_ref().filter(|(k, _)| *k == d.key).map(|(_, t)| *t);
        let first_top = y;
        let mut scrub_texts: Vec<(Option<String>, Option<f64>, Option<f64>)> = Vec::new();
        for (li, (key, label, level, charging)) in lanes.iter().enumerate() {
            let (top, bottom) = (y, y + lane_h);
            if li > 0 {
                // Solid line between the two buds' charts.
                let mid = top - lane_gap / 2;
                for x in x0..x1 {
                    cv.blend(x, mid, grid, 200);
                }
            }
            for gy in [top, (top + bottom) / 2, bottom] {
                let mut x = x0;
                while x < x1 {
                    cv.blend(x, gy, grid, 255);
                    x += px(4.0).max(2);
                }
            }
            let to_yf = |l: f64| bottom - ((bottom - top) as f64 * l.clamp(0.0, 100.0) / 100.0).round() as i32;
            let to_y = |l: u8| to_yf(l as f64);
            let lane_now = *level >= 0;
            let series = if label.is_none() { series.clone() } else { self.history.series(key) };
            let lane_est = if label.is_none() {
                est
            } else {
                let st = batteryhub::stats::compute(&series, lane_now.then_some((*level, *charging)));
                if !lane_now || *level >= 100 {
                    None
                } else if *charging {
                    st.charge_estimate()
                } else {
                    st.discharge_estimate()
                }
            };
            let segs = batteryhub::history::segments(&series, from, now);
            for seg in &segs {
                for pair in seg.windows(2) {
                    let (a, b) = (pair[0], pair[1]);
                    // Steps, not slopes: a level holds until the next reading. The step takes the
                    // colour of its level, the drop (or rise) the colour of the level it reaches.
                    cv.line(to_x(a.t), to_y(a.level), to_x(b.t), to_y(a.level), lw, level_c(a.level as f64, a.charging()));
                    cv.line(to_x(b.t), to_y(a.level), to_x(b.t), to_y(b.level), lw, level_c(b.level as f64, b.charging()));
                }
            }
            // Dotted "now" line in the middle.
            let mut yy = top;
            while yy < bottom {
                cv.blend(xm, yy, grid, 255);
                yy += px(4.0).max(2);
            }
            // Forecast: dashed, from the current level until empty (or full), then level.
            let level_now = (*level).clamp(0, 100) as f64;
            if let Some(e) = lane_est {
                let room = if *charging { 100.0 - level_now } else { level_now };
                let reach = now + ((room / e.rate) * 3600.0).min((to - now) as f64) as u64;
                let end_level = batteryhub::stats::project(level_now, e.rate, *charging, reach - now);
                // On battery the forecast turns red where it reaches the red-warning level.
                let th_f = th as f64;
                let cross = (!*charging && level_now > th_f && end_level < th_f)
                    .then(|| now + ((level_now - th_f) / e.rate * 3600.0) as u64)
                    .filter(|&t| t > now && t < reach);
                match cross {
                    Some(t) => {
                        cv.dashed(xm, to_yf(level_now), to_x(t), to_yf(th_f), lw, ok_c, px(5.0));
                        cv.dashed(to_x(t), to_yf(th_f), to_x(reach), to_yf(end_level), lw, low_c, px(5.0));
                    }
                    None => cv.dashed(xm, to_yf(level_now), to_x(reach), to_yf(end_level), lw, level_c(level_now, *charging), px(5.0)),
                }
                if reach < to {
                    cv.dashed(to_x(reach), to_yf(end_level), x1, to_yf(end_level), lw, level_c(end_level, *charging), px(5.0));
                }
            }
            if let Some(last) = segs.last().and_then(|s| s.last()) {
                cv.disc(to_x(last.t), to_y(last.level), px(3.5), level_c(last.level as f64, last.charging()));
            }
            if let Some(l) = label {
                let m = mask(l, small_f, light);
                cv.draw(&m, x0 + px(3.0), top + px(2.0), if lane_now { fg } else { dim }, 255);
            }
            // The hour under the mouse.
            if let Some(t) = scrub {
                let open_until = if lane_now { now } else { 0 };
                let value_at = |t: u64| -> Option<f64> {
                    if t <= now {
                        batteryhub::stats::level_at(&series, t, open_until).map(|p| p.level as f64)
                    } else {
                        lane_est.map(|e| batteryhub::stats::project(level_now, e.rate, *charging, t - now))
                    }
                };
                let sx = to_x(t);
                for yy in top..=bottom {
                    cv.blend(sx, yy, dim, 255);
                }
                let v = if t.abs_diff(now) < 90 && lane_now { Some(level_now) } else { value_at(t) };
                if let Some(v) = v {
                    cv.disc(sx, to_yf(v), px(3.5), level_c(v, *charging && t >= now));
                }
                scrub_texts.push((label.clone(), v, value_at(t.saturating_sub(3600))));
            }
            y = bottom + lane_gap;
        }
        let bottom = y - lane_gap;
        self.card_chart_y = (first_top, bottom);
        let title_text = match scrub {
            Some(t) => {
                let clock = if t.abs_diff(now) < 90 {
                    tr("Now")
                } else {
                    let l = batteryhub::dashboard::local(t);
                    format!("{:02}:{:02}", l.hour, l.minute)
                };
                let approx = if t > now { "≈ " } else { "" };
                let parts: Vec<String> = scrub_texts
                    .iter()
                    .map(|(label, v, before)| {
                        let side = label.as_ref().map(|l| format!("{l} ")).unwrap_or_default();
                        match v {
                            // One chart: the level and its change over the hour before.
                            Some(v) if label.is_none() => {
                                let change = before.map(|p| format!("   {} / 1 h", fmt_change(v - p))).unwrap_or_default();
                                format!("{approx}{}%{change}", v.round())
                            }
                            Some(v) => format!("{side}{approx}{}%", v.round()),
                            None if label.is_none() => tr("no reading"),
                            None => format!("{side}-"),
                        }
                    })
                    .collect();
                let forecast = if t > now && scrub_texts.iter().any(|p| p.1.is_some()) { format!("   ({})", tr("forecast")) } else { String::new() };
                format!("{clock}   {}{forecast}", parts.join("   "))
            }
            None => tr("Last 12 hours and the next 12 (forecast)"),
        };
        let title = mask(&title_text, small_f, light);
        cv.draw(&title, pad, title_y, if scrub.is_some() { fg } else { dim }, 255);
        y = bottom + px(10.0);
        let ago = mask(&tr("12h ago"), small_f, light);
        cv.draw(&ago, x0, y, dim, 255);
        let nowm = mask(&tr("Now"), small_f, light);
        cv.draw(&nowm, xm - nowm.w / 2, y, dim, 255);
        let ahead = mask(&tr("in 12h"), small_f, light);
        cv.draw(&ahead, x1 - ahead.w, y, dim, 255);
        // As much room under the bottom labels as above the header.
        let h = (y + px(14.0) + px(18.0)).min(tall);
        cv.px.truncate((w * h) as usize);
        (w, h, cv.px)
    }

    /// Shows the card for device `i` above (or below) its part of `strip`.
    fn show_card(&mut self, i: usize, strip: HWND, from: i32, to: i32) {
        let Some(d) = self.visible_at(i).cloned() else { return };
        if self.card.0.is_null() {
            self.card = create_card(self.main);
        }
        if self.card.0.is_null() {
            return;
        }
        let content = self.card_content(&d);
        let (w, h) = (content.w, content.h);
        unsafe {
            let mut rc = RECT::default();
            let _ = GetWindowRect(strip, &mut rc);
            let mut mi = MONITORINFO { cbSize: size_of::<MONITORINFO>() as u32, ..Default::default() };
            let _ = GetMonitorInfoW(MonitorFromWindow(strip, MONITOR_DEFAULTTONEAREST), &mut mi);
            let gap = (8.0 * self.scale()) as i32;
            let work = mi.rcWork;
            let (x, y, slide) = if self.vertical {
                // Beside the taskbar, level with the hovered device (no slide: it fades in).
                let mid = (mi.rcMonitor.left + mi.rcMonitor.right) / 2;
                let x = if rc.left < mid { rc.right + gap } else { rc.left - w - gap };
                let y = (rc.top + (from + to) / 2 - h / 2).clamp(work.top + gap, (work.bottom - h - gap).max(work.top));
                // Slides 10 px sideways, away from the taskbar.
                (x, y, (10.0 * self.scale()) as i32 * if x > rc.left { -1 } else { 1 })
            } else {
                let x = (rc.left + (from + to) / 2 - w / 2).clamp(work.left + gap, (work.right - w - gap).max(work.left));
                let y = if rc.top - h - gap >= work.top { rc.top - h - gap } else { rc.bottom + gap };
                // Slides 10 px towards its place: up when above the taskbar, down when below it.
                (x, y, (10.0 * self.scale()) as i32 * if y < rc.top { 1 } else { -1 })
            };
            let was_shown = self.card_anim.visible && self.card_anim.showing;
            let old_key = self.card_anim.content.as_ref().map(|c| c.key.clone());
            let same = was_shown && old_key.as_deref() == Some(d.key.as_str());
            let old = std::mem::take(&mut self.card_anim);
            // Already open on another device: blend the old card into the new one. A switch while
            // another is still running starts from what is on screen now (no jump back), and the
            // card that is more visible at that moment is the one that fades out.
            let prev = match (&old.content, was_shown && !same) {
                (Some(c), true) => {
                    let outgoing = match (&old.prev, old.at) {
                        (Some((_, _, p)), Some(at)) if at.elapsed().as_secs_f32() * 1000.0 < CARD_CROSS_MS * 0.5 => p.clone(),
                        _ => c.clone(),
                    };
                    let (dx, dw) = if old.drawn.1 > 0 { old.drawn } else { (old.x, c.w) };
                    Some((dx, dw, outgoing))
                }
                _ => None,
            };
            let crossing = prev.is_some();
            let prev_y = if old.drawn.1 > 0 { old.drawn_y } else { old.y };
            let prev_h = if old.drawn_h > 0 { old.drawn_h } else { old.content.as_ref().map_or(h, |c| c.h) };
            let (bg, border) = self.card_colors();
            let radius = (8.0 * self.scale()).round() as i32;
            let scale = self.scale();
            self.card_anim =
                CardAnim {
                at: old.at,
                showing: true,
                visible: true,
                x,
                y,
                slide,
                content: Some(content),
                prev,
                drawn: old.drawn,
                vertical: self.vertical,
                prev_y,
                drawn_y: old.drawn_y,
                prev_h,
                drawn_h: old.drawn_h,
                bg,
                border,
                radius,
                scale,
            };
            if crossing {
                self.card_anim.at = Some(Instant::now());
                SetTimer(Some(self.main), TIMER_CARD, 15, None);
            } else if same && self.card_anim.at.is_none() {
                // Same device, new values: swap the content at once.
                self.card_frame(1.0);
            } else if was_shown && !same {
                // Another device whose card has another height (e.g. earbuds with two charts):
                // no cross-fade between those, so the new card takes over at once. Before, it
                // kept showing the old device, or picked up the old card's half-done animation.
                self.card_anim.at = None;
                self.card_frame(1.0);
            } else {
                if !was_shown {
                    self.card_anim.at = Some(Instant::now());
                    self.card_frame(0.0);
                }
                SetTimer(Some(self.main), TIMER_CARD, 15, None);
            }
            let _ = SetWindowPos(self.card, Some(HWND_TOPMOST), 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE | SWP_SHOWWINDOW);
        }
    }

    /// The mouse left the strip. An open card stays while the mouse moves onto it (the gap
    /// between the two is crossed in a moment); TIMER_AWAY then watches where it is.
    fn leave_strip(&mut self) {
        self.tracking = false;
        if !self.card.0.is_null() && self.card_anim.visible && self.card_anim.showing {
            self.card_away = Some(Instant::now());
            unsafe {
                SetTimer(Some(self.main), TIMER_AWAY, 50, None);
            }
        } else {
            self.hide_tip();
            trim_memory();
        }
    }

    /// TIMER_AWAY: keeps the card while the mouse is on it, and closes it once the mouse has been
    /// on neither the card nor the strip for a moment.
    fn away_step(&mut self) {
        let mut pt = POINT::default();
        let under = unsafe { GetCursorPos(&mut pt).is_ok().then(|| WindowFromPoint(pt)) };
        if under.is_some_and(|w| w == self.card) && self.card_anim.showing {
            self.card_away = None;
            return;
        }
        self.set_card_scrub(None);
        let since = *self.card_away.get_or_insert_with(Instant::now);
        if since.elapsed().as_millis() >= CARD_AWAY_MS {
            self.hide_tip();
            trim_memory();
        }
    }

    /// Mouse on the card: the hour under it on the chart (whole hours, or now) is shown.
    fn card_mouse(&mut self) {
        let Some(content) = self.card_anim.content.clone() else { return };
        if !self.card_anim.showing || self.card_anim.prev.is_some() {
            return;
        }
        self.card_away = None;
        let (mut pt, mut rc) = (POINT::default(), RECT::default());
        unsafe {
            if GetCursorPos(&mut pt).is_err() || GetWindowRect(self.card, &mut rc).is_err() {
                return;
            }
        }
        let (cx, cy) = (pt.x - rc.left, pt.y - rc.top);
        let pad = (16.0 * self.card_anim.scale).round() as i32;
        let (x0, x1) = (pad, content.w - pad);
        let (top, bottom) = self.card_chart_y;
        let on_chart = card_opts(&content.key).0 && cy >= top - pad && cy <= bottom + pad && cx >= x0 - pad / 2 && cx <= x1 + pad / 2;
        let pick = on_chart.then(|| {
            let now = batteryhub::history::now_secs();
            let f = ((cx - x0) as f64 / (x1 - x0).max(1) as f64).clamp(0.0, 1.0);
            (content.key.clone(), snap_hour(now.saturating_sub(12 * 3600) as f64 + f * 24.0 * 3600.0, now))
        });
        self.set_card_scrub(pick);
    }

    fn set_card_scrub(&mut self, pick: Option<(String, u64)>) {
        if self.card_scrub == pick {
            return;
        }
        self.card_scrub = pick;
        // Draws the card again with (or without) the hour, in place.
        let Some(key) = self.card_anim.content.as_ref().map(|c| c.key.clone()) else { return };
        let Some(d) = self.devices.get(&key).map(|t| t.status.clone()) else { return };
        let content = self.card_content(&d);
        if self.card_anim.content.as_ref().is_some_and(|c| c.w == content.w && c.h == content.h) {
            self.card_anim.content = Some(content);
            if self.card_anim.at.is_none() {
                self.card_frame(1.0);
            }
        }
    }

    /// Fades the card out (then hides it).
    fn hide_card(&mut self) {
        if self.card.0.is_null() || !self.card_anim.visible || !self.card_anim.showing {
            return;
        }
        // A switch that is still running ends where it is: the fade-out starts from that frame.
        if self.card_anim.prev.take().is_some() {
            self.card_frame(1.0);
        }
        self.card_anim.showing = false;
        self.card_anim.at = Some(Instant::now());
        unsafe {
            SetTimer(Some(self.main), TIMER_CARD, 15, None);
        }
    }

    /// One animation frame: `t` 0..1 of the running fade-in (with a short rise), fade-out, or
    /// switch between devices (background glides and stretches, contents cross-fade). Drawn
    /// straight into the card's bitmap: no allocation per frame.
    fn card_frame(&mut self, t: f32) {
        let Some(content) = self.card_anim.content.clone() else { return };
        if self.card.0.is_null() {
            return;
        }
        let t = t.clamp(0.0, 1.0);
        let a = &self.card_anim;
        let (bg, border, radius, scale) = (a.bg, a.border, a.radius, a.scale);
        let h = content.h;
        let (pos, size, bx, bw, layers, alpha): (POINT, SIZE, i32, i32, Vec<Layer>, u8);
        let (drawn_y, bh): (i32, i32);
        if let (true, Some((ox, ow, old))) = (a.showing, &a.prev) {
            // Ease in-out, like the taskbar's window previews moving between buttons.
            let e = if t < 0.5 { 4.0 * t * t * t } else { 1.0 - (-2.0 * t + 2.0).powi(3) / 2.0 };
            let lerp = |p: i32, q: i32| p + ((q - p) as f32 * e).round() as i32;
            let (cx, cw) = (lerp(*ox, a.x), lerp(*ow, content.w));
            // Old content blurs away while the new one comes into focus.
            let (ro, rn) = ((BLUR_MAX * e * scale).round() as i32, (BLUR_MAX * (1.0 - e) * scale).round() as i32);
            // Height and top glide together: above the taskbar the bottom edge stays put, beside
            // a vertical one the card stays centred on the device it moves to.
            let (cy, ch) = (lerp(a.prev_y, a.y), lerp(a.prev_h, h).max(1));
            if a.vertical {
                // Devices are above one another: the whole card glides to the new one.
                pos = POINT { x: cx, y: cy };
                size = SIZE { cx: cw, cy: ch };
                (bx, bw) = (0, cw);
            } else {
                let (ux0, ux1) = (a.x.min(*ox), (a.x + content.w).max(ox + ow));
                pos = POINT { x: ux0, y: cy };
                size = SIZE { cx: ux1 - ux0, cy: ch };
                (bx, bw) = (cx - ux0, cw);
            }
            (drawn_y, bh) = (cy, ch);
            layers = vec![(old.clone(), 1.0 - e, ro), (content.clone(), e, rn)];
            alpha = 255;
            self.card_anim.drawn = (cx, cw);
        } else {
            let ease = 1.0 - (1.0 - t).powi(3); // ease-out cubic, like Windows 11 flyouts
            let (fade, dy) = if a.showing { (ease, a.slide as f32 * (1.0 - ease)) } else { (1.0 - t, 0.0) };
            // Comes into focus while appearing, goes slightly out of focus while disappearing.
            let r = if a.showing { BLUR_MAX * (1.0 - ease) } else { BLUR_MAX * 0.6 * t };
            let d = dy.round() as i32;
            (drawn_y, bh) = (a.y, h);
            pos = if a.vertical { POINT { x: a.x + d, y: a.y } } else { POINT { x: a.x, y: a.y + d } };
            size = SIZE { cx: content.w, cy: h };
            (bx, bw) = (0, content.w);
            layers = vec![(content.clone(), 1.0, (r * scale).round() as i32)];
            alpha = (fade * 255.0).round() as u8;
            self.card_anim.drawn = (a.x, content.w);
        }
        self.card_anim.drawn_y = drawn_y;
        self.card_anim.drawn_h = bh;
        let surface = match self.card_surface.take() {
            Some(s) if s.w >= size.cx && s.h >= size.cy => Some(s),
            // A quarter more than needed now: switching between neighbouring devices (the usual
            // case) then reuses the bitmap.
            _ => Surface::new(size.cx + content.w / 4, size.cy),
        };
        let Some(mut surface) = surface else { return };
        let stride = surface.w as usize;
        let dst = surface.pixels();
        let bgc = CardBg { bx, bw, h: bh, radius, bg, border };
        let t0 = Instant::now();
        compose_card(dst, stride, size.cx, size.cy, &bgc, &layers, &mut self.blur_scratch);
        let t1 = Instant::now();
        surface.present(self.card, pos, size, alpha);
        prof::add(&prof::FRAMES, 1);
        prof::add(&prof::COMPOSE_US, (t1 - t0).as_micros() as u64);
        prof::add(&prof::PRESENT_US, t1.elapsed().as_micros() as u64);
        self.card_surface = Some(surface);
    }

    /// TIMER_CARD: advances the card's animation; stops the timer (and hides) when done.
    fn card_step(&mut self) {
        let Some(at) = self.card_anim.at else {
            unsafe {
                let _ = KillTimer(Some(self.main), TIMER_CARD);
            }
            return;
        };
        let total = match (self.card_anim.showing, self.card_anim.prev.is_some()) {
            (true, true) => CARD_CROSS_MS,
            (true, false) => CARD_SHOW_MS,
            _ => CARD_HIDE_MS,
        };
        let t = at.elapsed().as_secs_f32() * 1000.0 / total;
        self.card_frame(t);
        if t >= 1.0 {
            self.card_anim.at = None;
            if self.card_anim.prev.take().is_some() {
                self.card_frame(1.0); // end of a cross-fade: only the new card, at its own size
            }
            unsafe {
                let _ = KillTimer(Some(self.main), TIMER_CARD);
                if !self.card_anim.showing {
                    let _ = ShowWindow(self.card, SW_HIDE);
                    prof::report();
                    // Closed: the bitmap, blur buffers and cached contents go back to Windows.
                    self.card_anim = CardAnim::default();
                    self.card_surface = None;
                    self.blur_scratch = BlurScratch::default();
                    self.card_cache.clear();
                }
            }
        }
    }

    // ---- hover tooltip -------------------------------------------------------------------------

    fn create_tooltip(&mut self) {
        unsafe {
            let Ok(tip) = CreateWindowExW(
                WS_EX_TOPMOST | WS_EX_TOOLWINDOW,
                TOOLTIPS_CLASSW,
                None,
                WS_POPUP | WINDOW_STYLE(TTS_ALWAYSTIP | TTS_NOPREFIX),
                0,
                0,
                0,
                0,
                Some(self.main),
                None,
                GetModuleHandleW(None).ok().map(|m| m.into()),
                None,
            ) else {
                return;
            };
            let mut ti = tool_info(self.main, &mut [0u16]);
            SendMessageW(tip, TTM_ADDTOOLW, None, Some(LPARAM(&mut ti as *mut _ as isize)));
            SendMessageW(tip, TTM_SETMAXTIPWIDTH, None, Some(LPARAM(480)));
            self.tip = tip;
        }
    }

    /// Text shown when hovering a device, short: "PRO 2 LIGHTSPEED: 96%" (+ charging / asleep).
    fn tip_text(&self, i: usize) -> String {
        let devices = self.visible();
        let Some(d) = devices.get(i) else {
            return tr("BatteryHub: no devices found");
        };
        let level = d.level();
        let numeric = level.ends_with('%');
        let state = if d.asleep {
            format!(" ({})", tr("asleep"))
        } else if d.is_full() && numeric {
            format!(" ({})", tr("full"))
        } else if d.charging && numeric {
            format!(" ({})", tr("charging"))
        } else {
            String::new()
        };
        format!("{}: {level}{state}", d.name)
    }

    /// Mouse at (x, y) on a strip: the device under it (along x, or along y on a vertical taskbar).
    fn hover(&mut self, on: HWND, x: i32, y: i32) {
        if MENU_OPEN.load(std::sync::atomic::Ordering::Relaxed) {
            return;
        }
        if self.drag.is_some() {
            self.drag_to(if self.vertical { y } else { x });
            return;
        }
        let x = if self.vertical { y } else { x };
        let hit = self.hits.iter().find(|h| x >= h.0 && x < h.1).map(|h| (h.2, h.0, h.1));
        let mode = hit.and_then(|h| self.visible_at(h.0)).map_or(settings::HoverMode::Card, |d| settings::hover_mode(SETTINGS_KEY, &d.key));
        // The hover highlight (like Windows' own taskbar buttons) in every mode, "Nothing" included.
        let _ = mode;
        self.set_hovered(on);
        if self.card_away.take().is_some() {
            unsafe {
                let _ = KillTimer(Some(self.main), TIMER_AWAY);
            }
        }
        if self.tip.0.is_null() {
            return;
        }
        if on != self.tip_on {
            self.tip_on = on;
            self.tracking = false;
            self.tip_for = None;
        }
        unsafe {
            if !self.tracking {
                let mut tme = TRACKMOUSEEVENT { cbSize: size_of::<TRACKMOUSEEVENT>() as u32, dwFlags: TME_LEAVE, hwndTrack: on, dwHoverTime: 0 };
                self.tracking = TrackMouseEvent(&mut tme).is_ok();
            }
            let key = hit.map(|h| h.0).unwrap_or(usize::MAX);
            if self.tip_for == Some(key) {
                return;
            }
            self.tip_for = Some(key);
            // The card (name, level, last 24 hours) above the hovered device, or the short
            // tooltip, or nothing (the device's "On hover" setting); nothing between devices.
            match (hit, mode) {
                (Some((i, from, to)), settings::HoverMode::Card) => {
                    self.tooltip_off();
                    self.show_card(i, on, from, to)
                }
                (Some((i, from, to)), settings::HoverMode::Tip) => {
                    self.hide_card();
                    self.tooltip_on(i, on, from, to);
                }
                _ => {
                    self.tooltip_off();
                    self.hide_card()
                }
            }
        }
    }

    /// The short tooltip ("Mouse: 80% (charging)") above (or beside) device `i` of `strip`.
    fn tooltip_on(&mut self, i: usize, strip: HWND, from: i32, to: i32) {
        unsafe {
            ui::set_tooltip_theme(self.tip, !self.light);
            let mut text: Vec<u16> = self.tip_text(i).encode_utf16().chain(std::iter::once(0)).collect();
            let mut ti = tool_info(self.main, &mut text);
            SendMessageW(self.tip, TTM_UPDATETIPTEXTW, None, Some(LPARAM(&mut ti as *mut _ as isize)));
            SendMessageW(self.tip, TTM_TRACKACTIVATE, Some(WPARAM(1)), Some(LPARAM(&mut ti as *mut _ as isize)));
            let size = SendMessageW(self.tip, TTM_GETBUBBLESIZE, None, Some(LPARAM(&mut ti as *mut _ as isize))).0;
            let (tw, th) = ((size & 0xFFFF) as i32, ((size >> 16) & 0xFFFF) as i32);
            let mut rc = RECT::default();
            let _ = GetWindowRect(strip, &mut rc);
            let gap = (4.0 * self.scale()) as i32;
            let (cx, cy) = if self.vertical {
                let mut mi = MONITORINFO { cbSize: size_of::<MONITORINFO>() as u32, ..Default::default() };
                let _ = GetMonitorInfoW(MonitorFromWindow(strip, MONITOR_DEFAULTTONEAREST), &mut mi);
                let left_side = rc.left < (mi.rcMonitor.left + mi.rcMonitor.right) / 2;
                (if left_side { rc.right + gap } else { rc.left - tw - gap }, rc.top + (from + to) / 2 - th / 2)
            } else {
                let mut mi = MONITORINFO { cbSize: size_of::<MONITORINFO>() as u32, ..Default::default() };
                let _ = GetMonitorInfoW(MonitorFromWindow(strip, MONITOR_DEFAULTTONEAREST), &mut mi);
                let above = rc.top - th - gap >= mi.rcMonitor.top;
                (rc.left + (from + to) / 2 - tw / 2, if above { rc.top - th - gap } else { rc.bottom + gap })
            };
            let pos = ((cy as u32 & 0xFFFF) << 16) | (cx as u32 & 0xFFFF);
            SendMessageW(self.tip, TTM_TRACKPOSITION, None, Some(LPARAM(pos as isize)));
        }
    }

    fn tooltip_off(&mut self) {
        if !self.tip.0.is_null() {
            unsafe {
                let mut ti = tool_info(self.main, &mut [0u16]);
                SendMessageW(self.tip, TTM_TRACKACTIVATE, Some(WPARAM(0)), Some(LPARAM(&mut ti as *mut _ as isize)));
            }
        }
    }

    fn hide_tip(&mut self) {
        self.set_hovered(HWND::default());
        self.card_away = None;
        self.card_scrub = None;
        unsafe {
            let _ = KillTimer(Some(self.main), TIMER_AWAY);
        }
        self.hide_card();
        self.tracking = false;
        self.tip_for = None;
        if !self.tip.0.is_null() {
            unsafe {
                let mut ti = tool_info(self.main, &mut [0u16]);
                SendMessageW(self.tip, TTM_TRACKACTIVATE, Some(WPARAM(0)), Some(LPARAM(&mut ti as *mut _ as isize)));
            }
        }
    }

    // ---- polling -------------------------------------------------------------------------------

    fn start_poll(&mut self) {
        if self.polling {
            // A read (full or quick) is running: if this one is for a device change, do it right
            // after, instead of losing it.
            if self.devchange || self.forget {
                self.pending_change = true;
            }
            return;
        }
        self.polling = true;
        // Enumerate the devices again only when something may have changed; a periodic read
        // reuses the device list (and still notices added / removed HID devices).
        let rescan = !self.scanned || self.devchange || self.forget;
        self.scanned = true;
        dbg_log(&format!("poll started (device change: {}, rescan: {rescan}, interval: {} min)", self.devchange, refresh_minutes()));
        ui::poll_async(self.main, WM_POLL_DONE, rescan);
    }

    /// Quick read of headset dongles and of receivers whose device is off or asleep (switching a
    /// headset on / off or waking
    /// a mouse is not a device change for Windows).
    fn start_quick(&mut self) {
        if self.polling || !refresh_on_change() {
            return;
        }
        let mut ids: HashSet<(u16, u16)> = self.offline_hw.clone();
        ids.extend(self.devices.values().filter(|t| t.status.asleep).filter_map(|t| t.status.hw));
        // Headsets on a 2.4 GHz dongle are switched off and on all the time, and the dongle stays
        // plugged in, so Windows reports nothing: check them too (one short status report each).
        ids.extend(self.devices.values().filter(|t| matches!(t.status.kind, DeviceKind::Headset | DeviceKind::Earbuds)).filter_map(|t| t.status.hw));
        // AirPods only broadcast their state: listen for a moment so a bud taken out of the case
        // (or put back) shows within seconds.
        let airpods = self.devices.keys().any(|k| k.starts_with("airpods:"));
        if ids.is_empty() && !airpods {
            return;
        }
        self.polling = true;
        let ids: Vec<(u16, u16)> = ids.into_iter().collect();
        dbg_log(&format!("quick read of {ids:04X?}{}", if airpods { " + AirPods" } else { "" }));
        let ids2 = ids.clone();
        QUICK_IDS.with(|q| *q.borrow_mut() = ids);
        ui::run_async(self.main, WM_QUICK_DONE, move || {
            let mut out = if ids2.is_empty() { Vec::new() } else { batteryhub::device::poll_hardware(&ids2) };
            if airpods {
                out.extend(batteryhub::device::poll_airpods());
            }
            out
        });
    }

    /// Merges a quick read: only devices behind the receivers in `ids` are updated or removed.
    fn on_quick_result(&mut self, fresh: Vec<DeviceStatus>, ids: &[(u16, u16)]) {
        self.polling = false;
        let keys: HashSet<String> = fresh.iter().map(|s| s.key.clone()).collect();
        self.devices.retain(|k, t| {
            let Some(hw) = t.status.hw else { return true };
            if !ids.contains(&hw) || keys.contains(k) {
                return true;
            }
            let present = batteryhub::device::hid_present(hw);
            match batteryhub::device::missing_device(Some(hw), present, t.status.grace_sec, t.seen.elapsed().as_secs(), MIN_GRACE_SEC) {
                Missing::Remove => false,
                Missing::Asleep => {
                    t.status.asleep = true;
                    true
                }
                Missing::Keep => true,
            }
        });
        for id in ids {
            self.offline_hw.remove(id);
        }
        self.merge(fresh);
        if std::mem::take(&mut self.pending_change) {
            self.devchange = true;
            self.start_poll();
        }
    }

    /// Adds / updates the devices of a read; devices reporting "off" are removed and their
    /// receiver is remembered for quick checks.
    fn merge(&mut self, fresh: Vec<DeviceStatus>) {
        self.record_history(&fresh);
        self.remember_devices(&fresh);
        let now = Instant::now();
        for mut s in fresh {
            if !self.order.contains(&s.key) {
                self.order.push(s.key.clone());
                settings::apply_order(&mut self.order, &self.saved_order);
                self.reordered = true;
            }
            if !s.connected {
                if let Some(hw) = s.hw {
                    self.offline_hw.insert(hw);
                }
                self.devices.remove(&s.key);
                continue;
            }
            let reported = std::mem::take(&mut s.name);
            s.name = self.names.get(&s.key).cloned().unwrap_or_else(|| reported.clone());
            self.check_critical(&s);
            self.devices.insert(s.key.clone(), Tracked { status: s, seen: now, reported });
        }
        self.order.retain(|k| self.devices.contains_key(k));
        self.paint();
        self.send_to_dashboards();
    }

    /// Every device keeps its place: one seen for the first time goes to the far left (saved).
    /// Devices are dated as seen (at most hourly), and those not seen for 7 days are forgotten.
    fn remember_devices(&mut self, fresh: &[DeviceStatus]) {
        let connected: Vec<String> = fresh.iter().filter(|s| s.connected && !s.key.starts_with("demo:")).map(|s| s.key.clone()).collect();
        let new: Vec<String> = connected.iter().filter(|k| !self.saved_order.contains(k)).cloned().collect();
        if !new.is_empty() {
            self.saved_order = settings::with_new_first(&self.saved_order, &new);
            settings::set_order(SETTINGS_KEY, &self.saved_order);
            dbg_log(&format!("new devices placed first: {new:?}"));
        }
        // The dashboard lists every device with saved history, also the ones not here now.
        for s in fresh.iter().filter(|s| s.connected && !s.key.starts_with("demo:")) {
            let reported = self.devices.get(&s.key).map(|t| t.reported.clone()).unwrap_or_else(|| s.name.clone());
            let line = batteryhub::dashboard::encode_status(&DeviceStatus { connected: false, percent: -1, ..s.clone() }, &reported);
            let sig = (s.name.clone(), s.kind as u8, s.via.clone());
            if self.known_saved.get(&s.key) != Some(&sig) && settings::set_known(SETTINGS_KEY, &s.key, &line) {
                self.known_saved.insert(s.key.clone(), sig);
            }
        }
        let now = batteryhub::history::now_secs();
        let due: Vec<String> = connected.into_iter().filter(|k| self.seen_saved.get(k).is_none_or(|t| now.saturating_sub(*t) >= 3600)).collect();
        if !due.is_empty() && settings::mark_seen(SETTINGS_KEY, &due, now) {
            for k in due {
                self.seen_saved.insert(k, now);
            }
        }
        if now.saturating_sub(self.forgot_at) >= 3600 {
            self.forgot_at = now;
            let gone = settings::forget_unseen(SETTINGS_KEY, now);
            if !gone.is_empty() {
                dbg_log(&format!("forgot devices not seen for 7 days: {gone:?}"));
                for k in &gone {
                    self.history.remove(k);
                }
                self.history.mark_dirty();
                self.saved_order = settings::order(SETTINGS_KEY);
                self.names = settings::names(SETTINGS_KEY);
                self.hidden = settings::hidden(SETTINGS_KEY);
            }
        }
    }

    /// Two devices swap places on the strip (and in the menu); the order is saved.
    fn swap_devices(&mut self, a: &str, b: &str) {
        if a == b {
            return;
        }
        self.saved_order = settings::swapped(&self.order, &self.saved_order, a, b);
        settings::set_order(SETTINGS_KEY, &self.saved_order);
        settings::apply_order(&mut self.order, &self.saved_order);
        self.reordered = true;
        self.card_cache.clear();
        self.paint();
    }

    /// While dragging: `a` takes the place of `b`, the devices between shift by one (saved).
    fn move_device(&mut self, a: &str, b: &str) {
        self.saved_order = settings::moved(&self.order, &self.saved_order, a, b);
        settings::set_order(SETTINGS_KEY, &self.saved_order);
        settings::apply_order(&mut self.order, &self.saved_order);
        self.reordered = true;
        self.card_cache.clear();
        self.paint();
    }

    /// The items on the strip this frame, in order: the visible devices, the "no devices found"
    /// glyph once the first read found none (nothing before the first read), and the items that
    /// are leaving, at their old place. Starts the appear / leave animations.
    fn strip_items(&mut self, devices: &[DeviceStatus]) -> Vec<Item> {
        let mut want: Vec<(String, Option<DeviceStatus>)> = devices.iter().map(|d| (d.key.clone(), Some(d.clone()))).collect();
        if self.loaded && devices.is_empty() && !self.hide_empty {
            want.push((NONE_KEY.into(), None));
        }
        if self.manual && self.polling {
            want.push((REFRESH_KEY.into(), None));
        }
        let old = std::mem::take(&mut self.shown);
        // Gone since the last render: pops out.
        for (k, _) in &old {
            if !want.iter().any(|w| &w.0 == k) {
                self.presence.entry(k.clone()).or_insert(Presence { leaving: true, at: Instant::now() }).turn(true);
            }
        }
        // New: waits until what leaves has popped out, then appears, one after another.
        let wait = self
            .presence
            .values()
            .filter(|p| p.leaving)
            .map(|p| (POP_MS - p.at.elapsed().as_secs_f32() * 1000.0).max(0.0) as u64)
            .max()
            .unwrap_or(0);
        let mut n = 0;
        for (k, _) in &want {
            if let Some(p) = self.presence.get_mut(k) {
                p.turn(false);
            } else if !old.iter().any(|o| &o.0 == k) {
                let at = Instant::now() + std::time::Duration::from_millis(wait + n * STAGGER_MS);
                self.presence.insert(k.clone(), Presence { leaving: false, at });
                n += 1;
            }
        }
        // Leaving items stay where they were: after the item before them in the last render.
        let mut list: Vec<(String, Option<DeviceStatus>, bool)> = want.into_iter().map(|(k, d)| (k, d, true)).collect();
        for (j, (k, d)) in old.iter().enumerate() {
            if list.iter().any(|l| &l.0 == k) || !self.presence.get(k).is_some_and(|p| p.leaving) {
                continue;
            }
            let at = old[..j].iter().rev().find_map(|(before, _)| list.iter().position(|l| &l.0 == before)).map(|i| i + 1).unwrap_or(0);
            list.insert(at, (k.clone(), d.clone(), false));
        }
        let mut out = Vec::with_capacity(list.len());
        let mut vis = 0;
        for (key, dev, live) in list {
            let (f, p, done) = self.presence.get(&key).map(|p| p.frame()).unwrap_or((1.0, 1.0, false));
            if done {
                self.presence.remove(&key);
                if !live {
                    continue;
                }
            }
            let v = (live && dev.is_some()).then(|| {
                vis += 1;
                vis - 1
            });
            self.shown.push((key.clone(), dev.clone()));
            out.push(Item { key, dev, vis: v, f: if done { 1.0 } else { f }, p: if done { 1.0 } else { p } });
        }
        out
    }

    /// Where each device is drawn along the strip this frame: (offset from its place, blur radius,
    /// opacity 0-255). The dragged device follows the mouse; devices that changed places slide
    /// from where they were drawn, blurred while they move, like the card's contents.
    fn motion(&mut self, keys: &[String], ranges: &[(i32, i32)], len: i32, s: f32) -> Vec<(i32, i32, u32)> {
        let now = Instant::now();
        if std::mem::take(&mut self.reordered) {
            for (k, r) in keys.iter().zip(ranges) {
                if self.drag.as_deref() == Some(k.as_str()) {
                    continue;
                }
                if let Some(&was) = self.drawn_at.get(k) {
                    // Positions are kept from the end of the strip (it is anchored there).
                    let d = (len as f32 - was) - r.0 as f32;
                    if d.abs() >= 1.0 {
                        self.slides.insert(k.clone(), (d, now));
                    }
                }
            }
        }
        self.slides.retain(|_, (_, t0)| (t0.elapsed().as_secs_f32() * 1000.0) < SLIDE_MS);
        let mut out = Vec::with_capacity(keys.len());
        self.starts.clear();
        let before = std::mem::take(&mut self.drawn_at);
        self.strip_len = len;
        for (k, r) in keys.iter().zip(ranges) {
            let (off, blur, alpha) = if self.drag.as_deref() == Some(k.as_str()) {
                // Held by the mouse, kept on the strip.
                let want = self.drag_at - self.grab;
                let at = want.clamp(0, (len - (r.1 - r.0)).max(0));
                (at - r.0, 0, 200)
            } else if let Some((d, t0)) = self.slides.get(k) {
                let p: f32 = (t0.elapsed().as_secs_f32() * 1000.0 / SLIDE_MS).clamp(0.0, 1.0);
                let left = (1.0f32 - p).powi(3); // ease-out: what is left of the way
                let off = (d * left).round() as i32;
                // Blur with the speed: strongest at the start, gone when it settles.
                let blur = ((1.0 - p) * (1.0 - p) * 3.0 * s).round() as i32;
                (off, blur.min((d.abs() / 4.0) as i32), 255)
            } else if !self.presence.is_empty()
                && let Some(&was) = before.get(k)
            {
                // Moved aside by a device appearing or leaving: blurred with its speed.
                let moved = (was - (len - r.0) as f32).abs();
                (0, ((moved / 2.0).round() as i32).min((3.0 * s).round() as i32), 255)
            } else {
                (0, 0, 255)
            };
            self.starts.insert(k.clone(), r.0);
            self.drawn_at.insert(k.clone(), (len - (r.0 + off)) as f32);
            out.push((off, blur, alpha));
        }
        unsafe {
            if self.slides.is_empty() && self.presence.is_empty() {
                let _ = KillTimer(Some(self.main), TIMER_SLIDE);
            } else {
                SetTimer(Some(self.main), TIMER_SLIDE, 15, None);
            }
        }
        out
    }

    /// Left button down on a strip: the device under the mouse can be dragged to another place.
    fn start_drag(&mut self, strip: HWND, x: i32, y: i32) {
        let x = if self.vertical { y } else { x };
        let Some(i) = self.hits.iter().find(|h| x >= h.0 && x < h.1).map(|h| h.2) else { return };
        let Some(key) = self.visible_at(i).map(|d| d.key.clone()) else { return };
        self.drag_at = x;
        self.grab = x - self.starts.get(&key).copied().unwrap_or(x);
        self.drag = Some(key);
        unsafe {
            windows::Win32::UI::Input::KeyboardAndMouse::SetCapture(strip);
        }
    }

    /// While dragging: the device moves to the place under the mouse.
    fn drag_to(&mut self, x: i32) {
        let Some(key) = self.drag.clone() else { return };
        if x == self.drag_at {
            return;
        }
        self.drag_at = x;
        self.hide_tip();
        let hit = self.hits.iter().find(|h| x >= h.0 && x < h.1).copied();
        let mine = self.hits.iter().position(|h| self.visible_at(h.2).is_some_and(|d| d.key == key));
        if let (Some((from, to, i)), Some(j)) = (hit, mine)
            && let Some(other) = self.visible_at(i).map(|d| d.key.clone())
            && other != key
        {
            // Past the middle of the other device: it makes room (no flicker between two of
            // different widths).
            let mid = (from + to) / 2;
            let k = self.hits.iter().position(|h| h.2 == i).unwrap_or(j);
            if (k > j && x >= mid) || (k < j && x <= mid) {
                self.move_device(&key, &other);
                return;
            }
        }
        self.paint();
    }

    fn end_drag(&mut self) {
        if let Some(key) = self.drag.take() {
            unsafe {
                let _ = windows::Win32::UI::Input::KeyboardAndMouse::ReleaseCapture();
            }
            // Let go: the device slides into its place.
            if let (Some(&from_end), Some(&place)) = (self.drawn_at.get(&key), self.starts.get(&key)) {
                let d = (self.strip_len as f32 - from_end) - place as f32;
                if d.abs() >= 1.0 {
                    self.slides.insert(key, (d, Instant::now()));
                }
            }
            self.paint();
        }
    }

    /// Deletes every measurement of a device; it is measured again from the next reading.
    fn reset_history(&mut self, key: &str) {
        self.history.flush();
        self.history.remove(key);
        self.history.mark_dirty();
        self.save_history_now();
        self.card_cache.clear();
        batteryhub::dashboard::notify_history_changed();
        dbg_log(&format!("measurements of {key} deleted"));
    }

    /// Phones with "Rising level means charging" (experimental): a level above the last one marks
    /// the phone as charging until a level below the last one (e.g. 15 % saved, then 21 %:
    /// charging, until 82 % is followed by 81 %). The first level compared is the last one saved.
    fn infer_charging(&mut self, fresh: &mut [DeviceStatus]) {
        for s in fresh.iter_mut() {
            if s.kind != DeviceKind::Phone || s.percent < 0 || !s.connected || !settings::rise_charging(SETTINGS_KEY, &s.key) {
                continue;
            }
            let saved = self.history.latest(&s.key).map(|p| p.level as i32);
            let st = self.rising.entry(s.key.clone()).or_insert((saved.unwrap_or(s.percent), false));
            if s.percent > st.0 {
                st.1 = true;
            } else if s.percent < st.0 {
                st.1 = false;
            }
            st.0 = s.percent;
            if st.1 && !s.charging {
                s.charging = true;
                s.full = s.percent >= 100;
            }
        }
    }

    /// "Delete device" in the dashboard: forgets a disconnected device altogether (measurements,
    /// settings and its entry). A device that is connected right now is left alone.
    fn delete_device(&mut self, key: &str) {
        if self.devices.get(key).is_some_and(|t| t.status.connected) {
            return;
        }
        self.devices.remove(key);
        self.order.retain(|k| k != key);
        self.reset_history(key);
        settings::forget_device(SETTINGS_KEY, key);
        self.saved_order = settings::order(SETTINGS_KEY);
        self.names = settings::names(SETTINGS_KEY);
        self.hidden = settings::hidden(SETTINGS_KEY);
        self.paint();
        self.send_to_dashboards();
        dbg_log(&format!("device {key} deleted"));
    }

    /// Fresh readings for open dashboards (they show the live level and state).
    fn send_to_dashboards(&self) {
        if batteryhub::dashboard::any_open() {
            batteryhub::dashboard::send_statuses(self.main, &self.dashboard_devices());
        }
    }

    /// The devices the dashboard lists: the ones read now (in the strip's order), then every other
    /// device that has saved history, shown as not connected with its last saved level.
    fn dashboard_devices(&self) -> Vec<(DeviceStatus, String)> {
        let mut list: Vec<(DeviceStatus, String)> =
            self.order.iter().filter_map(|k| self.devices.get(k)).map(|t| (t.status.clone(), t.reported.clone())).collect();
        for (key, line) in settings::known(SETTINGS_KEY) {
            if list.iter().any(|(s, _)| s.key == key) {
                continue;
            }
            let Some(last) = self.history.latest(&key) else { continue };
            let Some((mut s, reported)) = batteryhub::dashboard::decode_status(&line) else { continue };
            s.key = key;
            if let Some(n) = self.names.get(&s.key) {
                s.name = n.clone();
            }
            s.connected = false;
            s.percent = last.level as i32;
            s.charging = false;
            list.push((s, reported));
        }
        list
    }

    /// Names chosen with "Rename device" were changed: show them everywhere.
    fn reload_names(&mut self) {
        self.names = settings::names(SETTINGS_KEY);
        for (k, t) in self.devices.iter_mut() {
            t.status.name = self.names.get(k).cloned().unwrap_or_else(|| t.reported.clone());
        }
        self.card_cache.clear();
        self.paint();
        self.send_to_dashboards();
    }

    /// "Warn at 5%": one notification when a device on battery falls to 5% (see settings).
    fn check_critical(&mut self, s: &DeviceStatus) {
        if !s.connected || s.asleep || !settings::warn_critical(SETTINGS_KEY, &s.key) {
            return;
        }
        if self.critical.check(&s.key, s.percent, s.charging) {
            self.notify_low(&s.name, s.percent);
        }
    }

    /// Shows a Windows notification (a balloon of a temporary notification-area icon, which
    /// Windows 10 / 11 show as a toast). The icon is removed when the notification is gone.
    fn notify_low(&mut self, name: &str, level: i32) {
        let size = unsafe { windows::Win32::UI::HiDpi::GetSystemMetricsForDpi(SM_CXSMICON, windows::Win32::UI::HiDpi::GetDpiForSystem()) };
        let Some(icon) = ui::number_icon(&level.to_string(), ui::low_color(self.light), level, size, self.light) else { return };
        let mut d = self.tray_data(NOTIFY_UID);
        d.uFlags = NIF_ICON | NIF_TIP | NIF_MESSAGE | NIF_INFO;
        d.uCallbackMessage = WM_TRAY;
        d.hIcon = icon;
        d.dwInfoFlags = NIIF_WARNING;
        ui::fill_wide(&mut d.szTip, &format!("{name}: {level}%"));
        ui::fill_wide(&mut d.szInfoTitle, &trf("{name}: battery at {level}%", &[("name", name), ("level", &level.to_string())]));
        ui::fill_wide(&mut d.szInfo, &tr("Charge it soon. BatteryHub warns once per discharge (right-click the device to turn this off)."));
        unsafe {
            if !Shell_NotifyIconW(NIM_MODIFY, &d).as_bool() {
                let _ = Shell_NotifyIconW(NIM_ADD, &d);
            }
            if let Some(old) = self.notify_icon.replace(icon) {
                let _ = DestroyIcon(old);
            }
            SetTimer(Some(self.main), TIMER_NOTIFY, 60_000, None);
        }
        dbg_log(&format!("low-battery notification: {name} {level}%"));
    }

    /// Shows a Windows notification with the app's icon (see notify_low).
    fn notify_info(&mut self, title: &str, text: &str) {
        let size = unsafe { windows::Win32::UI::HiDpi::GetSystemMetricsForDpi(SM_CXSMICON, windows::Win32::UI::HiDpi::GetDpiForSystem()) };
        let icon = unsafe {
            let hinst = GetModuleHandleW(None).unwrap_or_default();
            let Ok(h) = LoadImageW(Some(hinst.into()), windows::core::PCWSTR(1 as _), IMAGE_ICON, size, size, LR_DEFAULTCOLOR) else { return };
            HICON(h.0)
        };
        let mut d = self.tray_data(NOTIFY_UID);
        d.uFlags = NIF_ICON | NIF_TIP | NIF_MESSAGE | NIF_INFO;
        d.uCallbackMessage = WM_TRAY;
        d.hIcon = icon;
        d.dwInfoFlags = NIIF_INFO;
        ui::fill_wide(&mut d.szTip, "BatteryHub");
        ui::fill_wide(&mut d.szInfoTitle, title);
        ui::fill_wide(&mut d.szInfo, text);
        unsafe {
            if !Shell_NotifyIconW(NIM_MODIFY, &d).as_bool() {
                let _ = Shell_NotifyIconW(NIM_ADD, &d);
            }
            if let Some(old) = self.notify_icon.replace(icon) {
                let _ = DestroyIcon(old);
            }
            SetTimer(Some(self.main), TIMER_NOTIFY, 60_000, None);
        }
    }

    /// Removes the temporary notification icon.
    fn end_notify(&mut self) {
        if let Some(icon) = self.notify_icon.take() {
            unsafe {
                let _ = Shell_NotifyIconW(NIM_DELETE, &self.tray_data(NOTIFY_UID));
                let _ = DestroyIcon(icon);
                let _ = KillTimer(Some(self.main), TIMER_NOTIFY);
            }
        }
    }

    /// Menu refresh: `devices` = full rescan that drops devices that are gone right away;
    /// otherwise only the battery levels are read again (devices keep their grace period).
    fn manual_refresh(&mut self, devices: bool) {
        self.forget |= devices;
        self.manual = true;
        self.start_poll();
        self.paint(); // shows the ↻ indicator
    }

    fn on_result(&mut self, mut fresh: Vec<DeviceStatus>) {
        fresh.extend(demo_devices());
        self.infer_charging(&mut fresh);
        self.polling = false;
        self.loaded = true;
        self.manual = false;
        self.devchange = false;
        if std::mem::take(&mut self.forget) {
            self.devices.clear();
            self.order.clear();
        }
        let keys: HashSet<String> = fresh.iter().map(|s| s.key.clone()).collect();
        // A device missing from this read:
        //  * read through a receiver / cable that is gone (unplugged): removed at once;
        //  * read through hardware that is still there: the device itself sleeps or missed one
        //    answer - keep the last value (dimmed while it sleeps) for its grace period;
        //  * Bluetooth / BLE / XInput devices are only reported while connected, so missing
        //    means disconnected: removed at once.
        self.devices.retain(|k, t| {
            if keys.contains(k) {
                return true;
            }
            let present = t.status.hw.is_some_and(batteryhub::device::hid_present);
            match batteryhub::device::missing_device(t.status.hw, present, t.status.grace_sec, t.seen.elapsed().as_secs(), MIN_GRACE_SEC) {
                Missing::Remove => false,
                Missing::Asleep => {
                    t.status.asleep = true;
                    true
                }
                Missing::Keep => true,
            }
        });
        self.offline_hw.clear();
        self.merge(fresh);
        if std::mem::take(&mut self.pending_change) {
            self.devchange = true;
            self.start_poll();
        }
    }
}

impl App {
    /// Re-reads the taskbar theme and TaskbarOffset (start-up and WM_SETTINGCHANGE only).
    fn refresh_settings(&mut self) {
        self.light = ui::taskbar_is_light();
        self.offset = batteryhub::util::reg_get_dword(SETTINGS_KEY, "TaskbarOffset").unwrap_or(0);
        let side = batteryhub::util::reg_get_dword(SETTINGS_KEY, "WidgetLeft").unwrap_or(0);
        self.align_left = side != 0;
        self.after_icons = side == 2;
        self.hide_empty = batteryhub::util::reg_get_dword(SETTINGS_KEY, "HideWhenEmpty").unwrap_or(0) != 0;
        self.offset_y = batteryhub::util::reg_get_dword(SETTINGS_KEY, "TaskbarOffsetY").unwrap_or(0) as i32;
        self.background = batteryhub::util::reg_get_dword(SETTINGS_KEY, "WidgetBackground").unwrap_or(0) != 0;
        self.icons_mode = batteryhub::util::reg_get_dword(SETTINGS_KEY, "NotificationIcons").unwrap_or(0) != 0;
        self.compact = batteryhub::util::reg_get_dword(SETTINGS_KEY, "CompactWidget").unwrap_or(0) != 0;
        self.choice = widget_choice();
    }
}

// ---- check for updates ---------------------------------------------------------------------

/// A check or download is running (the menu item is greyed out meanwhile).
static UPDATE_BUSY: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
const UPDATE_TITLE: &str = "BatteryHub - Check for updates";

/// Runs `work` on a worker thread and posts its boxed result to `hwnd` as `msg`.
fn post_from_thread<T: Send + 'static>(hwnd: HWND, msg: u32, work: impl FnOnce() -> T + Send + 'static) {
    let h = hwnd.0 as usize;
    std::thread::spawn(move || {
        let ptr = Box::into_raw(Box::new(work()));
        unsafe {
            if PostMessageW(Some(HWND(h as *mut c_void)), msg, WPARAM(0), LPARAM(ptr as isize)).is_err() {
                drop(Box::from_raw(ptr));
            }
        }
    });
}

/// The running check was started automatically: only "a new update is available" is shown.
static UPDATE_SILENT: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
/// The running download is a silent install: no message boxes, the setup runs without a window.
static UPDATE_QUIET: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

fn check_for_updates(main: HWND, silent: bool) {
    if UPDATE_BUSY.swap(true, std::sync::atomic::Ordering::Relaxed) {
        return;
    }
    UPDATE_SILENT.store(silent, std::sync::atomic::Ordering::Relaxed);
    post_from_thread(main, WM_UPDATE_CHECKED, batteryhub::update::check);
}

fn message(owner: HWND, text: &str, style: MESSAGEBOX_STYLE) -> MESSAGEBOX_RESULT {
    unsafe {
        let _ = SetForegroundWindow(owner);
        MessageBoxW(Some(owner), &windows::core::HSTRING::from(text), &windows::core::HSTRING::from(tr(UPDATE_TITLE)), style | MB_SETFOREGROUND | MB_TOPMOST)
    }
}

fn on_update_checked(main: HWND, check: batteryhub::update::Check) {
    use batteryhub::install::{label_of, version_label};
    use batteryhub::update::Check;
    trim_memory();
    let silent = UPDATE_SILENT.swap(false, std::sync::atomic::Ordering::Relaxed);
    if silent && !matches!(check, Check::Available(_)) {
        UPDATE_BUSY.store(false, std::sync::atomic::Ordering::Relaxed);
        if matches!(check, Check::Failed(_)) && AUTO_UPDATE_TRIES.fetch_add(1, std::sync::atomic::Ordering::Relaxed) < AUTO_UPDATE_RETRIES {
            unsafe {
                SetTimer(Some(main), TIMER_AUTO_UPDATE, AUTO_UPDATE_RETRY_MS, None);
            }
        }
        return;
    }
    match check {
        Check::UpToDate { latest } => {
            UPDATE_BUSY.store(false, std::sync::atomic::Ordering::Relaxed);
            message(
                main,
                &trf(
                    "No new updates.\n\nYou have the latest version ({current}).\nLatest release on GitHub: {latest}.",
                    &[("current", &version_label()), ("latest", &label_of(&latest))],
                ),
                MB_OK | MB_ICONINFORMATION,
            );
        }
        Check::Failed(e) => {
            UPDATE_BUSY.store(false, std::sync::atomic::Ordering::Relaxed);
            message(
                main,
                &trf(
                    "Could not check for updates:\n{error}\n\nNew versions are also on GitHub:\n{url}",
                    &[("error", &e.to_string()), ("url", &format!("https://github.com/{}/releases", batteryhub::update::REPO))],
                ),
                MB_OK | MB_ICONWARNING,
            );
        }
        // Automatic check with "Install updates silently": download and install, show nothing.
        Check::Available(r) if silent && silent_install() => {
            UPDATE_QUIET.store(true, std::sync::atomic::Ordering::Relaxed);
            post_from_thread(main, WM_UPDATE_DOWNLOADED, move || batteryhub::update::download(&r));
        }
        Check::Available(r) => {
            let text = trf(
                "A new update is available:\n\n        {current}  ->  {new}\n\nDo you want to update now?\n\nThe setup is downloaded from GitHub, checked against the release's SHA-256 checksum and started; it keeps your settings and autostart.",
                &[("current", &version_label()), ("new", &label_of(&r.version))],
            );
            if message(main, &text, MB_YESNO | MB_ICONQUESTION) == IDYES {
                post_from_thread(main, WM_UPDATE_DOWNLOADED, move || batteryhub::update::download(&r));
            } else {
                UPDATE_BUSY.store(false, std::sync::atomic::Ordering::Relaxed);
            }
        }
    }
}

fn on_update_downloaded(main: HWND, result: Result<batteryhub::update::Verified, String>) {
    UPDATE_BUSY.store(false, std::sync::atomic::Ordering::Relaxed);
    trim_memory();
    if UPDATE_QUIET.swap(false, std::sync::atomic::Ordering::Relaxed) {
        // No console window and no "Update finished" box afterwards. A failed download or start
        // is not shown either; the next start tries again.
        if let Ok(setup) = result {
            let _ = setup.start(&["/update", "/S", "/nonotify"], true);
        }
        return;
    }
    match result {
        // The setup closes this program (and starts the new version) itself.
        Ok(setup) => {
            let path = setup.path.clone();
            if let Err(e) = setup.start(&["/update"], false) {
                message(
                    main,
                    &trf("Could not start the setup:\n{error}\n\n{path}", &[("error", &e.to_string()), ("path", &path.display().to_string())]),
                    MB_OK | MB_ICONWARNING,
                );
            }
        }
        Err(e) => {
            message(
                main,
                &format!(
                    "The update could not be downloaded:
{e}"
                ),
                MB_OK | MB_ICONWARNING,
            );
        }
    }
}

/// "Install another version...": the setup kept next to the program opens on its version list
/// (any release, also an older one; verified like an update).
/// Opens a GitHub page in the default browser.
fn open_url(url: &str) {
    if !url.starts_with("https://github.com/") && url != DISCORD_URL && url != SUPPORT_URL {
        return;
    }
    unsafe {
        let _ = windows::Win32::UI::Shell::ShellExecuteW(None, w!("open"), &windows::core::HSTRING::from(url), None, None, SW_SHOWNORMAL);
    }
}

/// The latest releases (version, page), newest first, for the Help menu. Fetched in the
/// background at most once an hour (when the menu opens); empty until the first answer.
fn recent_releases() -> Vec<(String, String)> {
    type Releases = Option<(Instant, Vec<(String, String)>)>;
    static CACHE: std::sync::Mutex<Releases> = std::sync::Mutex::new(None);
    static BUSY: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
    let (list, stale) = match &*CACHE.lock().unwrap_or_else(|e| e.into_inner()) {
        Some((at, list)) => (list.clone(), at.elapsed() > std::time::Duration::from_secs(3600) || list.is_empty() && at.elapsed() > std::time::Duration::from_secs(60)),
        None => (Vec::new(), true),
    };
    if stale && !BUSY.swap(true, std::sync::atomic::Ordering::SeqCst) {
        std::thread::spawn(|| {
            let found = batteryhub::update::list_releases();
            if let Err(e) = &found {
                dbg_log(&format!("recent releases: {e}"));
            }
            let list: Vec<(String, String)> =
                found.map(|v| v.into_iter().filter(|r| !r.prerelease).take(HELP_RELEASES).map(|r| (r.version, r.page_url)).collect()).unwrap_or_default();
            dbg_log(&format!("recent releases: {} loaded", list.len()));
            *CACHE.lock().unwrap_or_else(|e| e.into_inner()) = Some((Instant::now(), list));
            BUSY.store(false, std::sync::atomic::Ordering::SeqCst);
        });
    }
    list
}

fn open_version_list(main: HWND) {
    let setup = std::env::current_exe().ok().and_then(|e| e.parent().map(|d| d.join("BatteryHub-Setup.exe")));
    match setup {
        Some(s) if s.exists() => {
            let _ = std::process::Command::new(s).arg("/versions").spawn();
        }
        _ => {
            message(
                main,
                &format!(
                    "The setup is not next to this program (it is kept there by an installation).

All versions are on GitHub:
https://github.com/{}/releases",
                    batteryhub::update::REPO
                ),
                MB_OK | MB_ICONINFORMATION,
            );
        }
    }
}

/// Hands memory that was only needed for a moment (a read, a Bluetooth check, a render) back to
/// Windows, so between those moments the program keeps well under 1 MB resident. Pages it needs
/// again come back from the standby list (soft faults), which costs microseconds.
fn trim_memory() {
    unsafe {
        let _ = SetProcessWorkingSetSize(GetCurrentProcess(), usize::MAX, usize::MAX);
    }
}

/// Battery refresh interval in minutes (menu choice, default 1 minute).
/// The language chosen in the menu: a language code, or "" for Windows' language.
fn language_choice() -> String {
    batteryhub::util::reg_get_string(SETTINGS_KEY, "Language").unwrap_or_default()
}

/// Switches the language ("" = Windows' language), saves the choice and redraws.
fn set_language(code: &str) {
    if code.is_empty() {
        batteryhub::util::reg_delete_value(SETTINGS_KEY, "Language");
    } else {
        batteryhub::util::reg_set_string(SETTINGS_KEY, "Language", code);
    }
    batteryhub::i18n::set_language(code);
    with_app(|a| {
        a.hide_tip();
        a.card_cache.clear();
        a.paint();
    });
}

fn refresh_minutes() -> u32 {
    batteryhub::util::reg_get_dword(SETTINGS_KEY, "RefreshMinutes").filter(|m| INTERVALS.iter().any(|(v, _)| v == m)).unwrap_or(1)
}

/// Refresh when a device connects or disconnects (default on). Read from the registry once and
/// cached (it is checked every few seconds); the menu updates the cache when it is toggled.
static ON_CHANGE: std::sync::atomic::AtomicU8 = std::sync::atomic::AtomicU8::new(2); // 2 = not read yet

fn refresh_on_change() -> bool {
    use std::sync::atomic::Ordering;
    match ON_CHANGE.load(Ordering::Relaxed) {
        2 => {
            let on = batteryhub::util::reg_get_dword(SETTINGS_KEY, "RefreshOnDeviceChange").unwrap_or(1) != 0;
            ON_CHANGE.store(on as u8, Ordering::Relaxed);
            on
        }
        v => v != 0,
    }
}

/// Check for updates when BatteryHub starts (default off).
fn auto_update() -> bool {
    batteryhub::util::reg_get_dword(SETTINGS_KEY, "AutoCheckUpdates").unwrap_or(0) != 0
}

/// With the automatic check: install a new version in the background without asking (default off).
fn silent_install() -> bool {
    batteryhub::util::reg_get_dword(SETTINGS_KEY, "SilentUpdates").unwrap_or(0) != 0
}

fn autostart_name() -> &'static str {
    batteryhub::install::TASKBAR.run_value.unwrap_or("BatteryHub Taskbar")
}

fn save_dword(name: &str, value: u32) {
    if let Some(k) = batteryhub::install::create(batteryhub::install::HKCU, SETTINGS_KEY) {
        k.set_dword(name, value);
    }
}

/// A full-screen window (game, video) is in front on the monitor of taskbar `bar`. Explorer
/// itself decides that: it takes such a monitor's taskbar out of the topmost band (it goes behind
/// the game), so the copy follows the taskbar. Guessing from the window's size hid it wrongly for
/// borderless windows that cover a monitor without being full-screen apps (e.g. Wallpaper Engine).
fn fullscreen_over(bar: HWND) -> bool {
    unsafe { GetWindowLongW(bar, GWL_EXSTYLE) as u32 & WS_EX_TOPMOST.0 == 0 }
}

/// EVENT_SYSTEM_FOREGROUND: tells the main window, which places the copies again.
unsafe extern "system" fn foreground_changed(
    _hook: windows::Win32::UI::Accessibility::HWINEVENTHOOK,
    _event: u32,
    _hwnd: HWND,
    _object: i32,
    _child: i32,
    _thread: u32,
    _time: u32,
) {
    unsafe {
        if let Ok(main) = FindWindowW(MAIN_CLASS, None) {
            let _ = PostMessageW(Some(main), WM_FOREGROUND, WPARAM(0), LPARAM(0));
        }
    }
}

/// Creates a (hidden) copy for another monitor's taskbar: a topmost popup owned by that taskbar,
/// not a child of it. Windows 11 composes child windows of the secondary taskbars late (their
/// animations stuttered, and a new copy could stay blank), top-level windows on time.
fn create_copy(taskbar: HWND) -> Option<HWND> {
    unsafe {
        let hinst = GetModuleHandleW(None).unwrap_or_default();
        let r = CreateWindowExW(
            WS_EX_LAYERED | WS_EX_NOACTIVATE | WS_EX_TOOLWINDOW | WS_EX_TOPMOST,
            STRIP_CLASS,
            w!(""),
            WS_POPUP,
            0,
            0,
            1,
            1,
            Some(taskbar),
            None,
            Some(hinst.into()),
            None,
        );
        if r.is_err() {
            dbg_log(&format!("CreateWindowExW (copy) failed: {:?}", windows::Win32::Foundation::GetLastError()));
        }
        r.ok()
    }
}

/// Stardock Start11's enhanced taskbar sits inside `Shell_TrayWnd` as `SDTaskbar` and fights
/// child-window Z-order; a topmost popup owned by `Shell_TrayWnd` stays cleanly above it.
fn has_sdtaskbar(bar: HWND) -> bool {
    unsafe {
        let mut after: Option<HWND> = None;
        while let Ok(h) = FindWindowExW(Some(bar), after, w!("#32770"), None) {
            if h.0.is_null() {
                break;
            }
            after = Some(h);
            let mut txt = [0u16; 32];
            let n = GetWindowTextW(h, &mut txt) as usize;
            if batteryhub::util::from_wide(&txt[..n]) == "SDTaskbar" {
                return true;
            }
        }
        false
    }
}

/// Creates a (hidden) strip window as a child of a taskbar.
fn create_strip(taskbar: HWND) -> Option<HWND> {
    unsafe {
        let hinst = GetModuleHandleW(None).unwrap_or_default();
        let r = CreateWindowExW(
            WS_EX_LAYERED | WS_EX_NOACTIVATE,
            STRIP_CLASS,
            w!(""),
            WS_CHILD | WS_CLIPSIBLINGS,
            0,
            0,
            1,
            1,
            Some(taskbar),
            None,
            Some(hinst.into()),
            None,
        );
        if r.is_err() {
            dbg_log(&format!("CreateWindowExW failed: {:?}", windows::Win32::Foundation::GetLastError()));
        }
        r.ok()
    }
}

/// Taskbars of the other monitors, left to right.
fn secondary_taskbars() -> Vec<HWND> {
    let mut out: Vec<(i32, i32, HWND)> = Vec::new();
    unsafe {
        let mut after: Option<HWND> = None;
        while let Ok(h) = FindWindowExW(None, after, w!("Shell_SecondaryTrayWnd"), None) {
            if h.0.is_null() {
                break;
            }
            after = Some(h);
            if !IsWindowVisible(h).as_bool() {
                continue;
            }
            let mut r = RECT::default();
            let _ = GetWindowRect(h, &mut r);
            out.push((r.left, r.top, h));
        }
    }
    out.sort_by_key(|o| (o.0, o.1));
    out.into_iter().map(|o| o.2).collect()
}

/// "Show widget on": "all", "main" (default) or the id of one other monitor. v1.2 stored a number
/// of monitors instead (1 = main only, more = all).
fn widget_choice() -> String {
    if let Some(v) = batteryhub::util::reg_get_string(SETTINGS_KEY, "WidgetMonitor").filter(|v| !v.is_empty()) {
        return v;
    }
    match batteryhub::util::reg_get_dword(SETTINGS_KEY, "WidgetMonitors") {
        Some(n) if n >= 2 => "all".into(),
        _ => "main".into(),
    }
}

fn monitor_info(bar: HWND) -> Option<MONITORINFOEXW> {
    unsafe {
        let mon = MonitorFromWindow(bar, MONITOR_DEFAULTTONULL);
        if mon.is_invalid() {
            return None;
        }
        let mut mi = MONITORINFOEXW::default();
        mi.monitorInfo.cbSize = size_of::<MONITORINFOEXW>() as u32;
        GetMonitorInfoW(mon, &mut mi.monitorInfo as *mut MONITORINFO).as_bool().then_some(mi)
    }
}

/// A monitor's lasting identity: its device interface name (survives reboots, Explorer restarts and
/// Windows renumbering the displays), else "\\.\DISPLAYn".
fn monitor_id(bar: HWND) -> String {
    let Some(mi) = monitor_info(bar) else { return String::new() };
    let device = batteryhub::util::from_wide(&mi.szDevice);
    unsafe {
        let mut dd = DISPLAY_DEVICEW { cb: size_of::<DISPLAY_DEVICEW>() as u32, ..Default::default() };
        if EnumDisplayDevicesW(&windows::core::HSTRING::from(device.as_str()), 0, &mut dd, 1 /* EDD_GET_DEVICE_INTERFACE_NAME */).as_bool() {
            let id = batteryhub::util::from_wide(&dd.DeviceID);
            if !id.is_empty() {
                return id;
            }
        }
    }
    device
}

/// "Display 2 (left)": the number Windows gives the display and where it is next to the main one.
fn monitor_label(bar: HWND) -> String {
    let Some(mi) = monitor_info(bar) else { return tr("Other monitor") };
    let device = batteryhub::util::from_wide(&mi.szDevice);
    let mut label = match device.find("DISPLAY") {
        Some(i) => trf("Display {number}", &[("number", &device[i + 7..])]),
        None => tr("Other monitor"),
    };
    unsafe {
        let mon = MonitorFromPoint(POINT { x: 0, y: 0 }, MONITOR_DEFAULTTOPRIMARY);
        let mut pm = MONITORINFO { cbSize: size_of::<MONITORINFO>() as u32, ..Default::default() };
        if GetMonitorInfoW(mon, &mut pm).as_bool() {
            let (m, p) = (mi.monitorInfo.rcMonitor, pm.rcMonitor);
            let dx = (m.left + m.right - p.left - p.right) / 2;
            let dy = (m.top + m.bottom - p.top - p.bottom) / 2;
            let side = if dx.abs() >= dy.abs() {
                if dx < 0 { n_("{display} (left)") } else { n_("{display} (right)") }
            } else if dy < 0 {
                n_("{display} (above)")
            } else {
                n_("{display} (below)")
            };
            label = trf(side, &[("display", &label)]);
        }
    }
    label
}

/// The model part of a monitor id ("AUO7EAD" in \\?\DISPLAY#AUO7EAD#4&...#{...}).
fn monitor_model(id: &str) -> &str {
    let Some(a) = id.find("DISPLAY#").map(|a| a + 8) else { return "" };
    id[a..].find('#').map(|b| &id[a..a + b]).unwrap_or("")
}

/// Index of the chosen monitor among `ids`, or None when it is not connected. A saved id that
/// matches none exactly still matches the only connected monitor of the same model (a laptop
/// panel's id changes when a MUX switch moves it to the other GPU).
fn find_monitor(ids: &[String], choice: &str) -> Option<usize> {
    if let Some(i) = ids.iter().position(|i| i == choice) {
        return Some(i);
    }
    let model = monitor_model(choice);
    if model.is_empty() {
        return None;
    }
    let same: Vec<usize> = (0..ids.len()).filter(|&i| monitor_model(&ids[i]) == model).collect();
    (same.len() == 1).then(|| same[0])
}

/// A strip window created by this process (a handle that outlived Explorer may have been reused by
/// someone else's window, which must never be destroyed).
/// Notification-area icon id for a device: stable (from its key), never 0, and different from the
/// ids already in use (a hash clash moves to the next free id).
fn tray_uid(key: &str, used: Vec<u32>) -> u32 {
    let mut uid = (batteryhub::util::fnv1a(key) & 0x7FFF_FFFF).max(1);
    while used.contains(&uid) {
        uid = uid.wrapping_add(1).max(1);
    }
    uid
}

fn is_our_strip(h: HWND) -> bool {
    unsafe {
        if h.0.is_null() || !IsWindow(Some(h)).as_bool() {
            return false;
        }
        let mut pid = 0u32;
        GetWindowThreadProcessId(h, Some(&mut pid));
        let mut class = [0u16; 64];
        let n = GetClassNameW(h, &mut class) as usize;
        pid == std::process::id() && String::from_utf16_lossy(&class[..n]) == "BatteryHub.Taskbar.Strip"
    }
}

/// "BatteryHub is free": shown once after a new installation.
fn free_notice() {
    let text = tr(FREE_NOTICE);
    unsafe {
        MessageBoxW(
            None,
            &windows::core::HSTRING::from(text),
            &windows::core::HSTRING::from(tr("BatteryHub is free")),
            MB_OK | MB_ICONINFORMATION | MB_SETFOREGROUND | MB_TOPMOST,
        );
    }
}

const FREE_NOTICE: &str = n_("BatteryHub is free and will always stay free.\n\nNobody should ever pay for it. If you paid someone for BatteryHub, you were scammed: ask them for a refund.\n\nThe only official place to get it is the GitHub page: github.com/ferloom/Wireless-Device-Battery-Monitor\n\nMade with love by ferloom.");

/// What the card of a device holds: (battery chart, time left). "Battery only" turns both off.
fn card_opts(key: &str) -> (bool, bool) {
    if settings::battery_only(SETTINGS_KEY, key) {
        return (false, false);
    }
    (settings::card_chart(SETTINGS_KEY, key), settings::card_time(SETTINGS_KEY, key))
}

fn tool_info(owner: HWND, text: &mut [u16]) -> TTTOOLINFOW {
    TTTOOLINFOW {
        cbSize: size_of::<TTTOOLINFOW>() as u32,
        uFlags: TTF_TRACK | TTF_ABSOLUTE,
        hwnd: owner,
        uId: 1,
        lpszText: windows::core::PWSTR(text.as_mut_ptr()),
        ..Default::default()
    }
}

fn dbg_log(msg: &str) {
    if std::env::var_os("BH_DEBUG").is_some() {
        use std::io::Write;
        if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(std::env::temp_dir().join("bh2.log")) {
            let _ = writeln!(f, "{msg}");
        }
    }
}

/// The right-click menu (strip and fallback icons): per-device warning levels, refresh options, exit.
/// The taskbar is set to hide automatically.
fn taskbar_autohides() -> bool {
    use windows::Win32::UI::Shell::{ABM_GETSTATE, APPBARDATA, SHAppBarMessage};
    let mut abd = APPBARDATA { cbSize: size_of::<APPBARDATA>() as u32, ..Default::default() };
    unsafe { SHAppBarMessage(ABM_GETSTATE, &mut abd) & 0x1 != 0 } // ABS_AUTOHIDE
}

/// Window that owns the context menu. A right-click on the widget inside a taskbar gives the menu to
/// that widget (a child of the taskbar): the taskbar then is the active window and stays shown while
/// the menu is open, also when it hides itself automatically (it hid and took the menu along when our
/// own window owned it). A copy on another monitor (a window of its own) owns its menu only while the
/// taskbars hide automatically; everything else (tray icon, card) uses our hidden main window.
/// `from` is the window that was right-clicked; the cursor position alone missed the widget where its
/// pixels are transparent.
unsafe fn menu_owner(main: HWND, from: Option<HWND>) -> HWND {
    unsafe {
        let hides = taskbar_autohides();
        let owner = match from {
            Some(h) if !h.0.is_null() && IsWindow(Some(h)).as_bool() => {
                let child = GetWindowLongW(h, GWL_STYLE) as u32 & WS_CHILD.0 != 0;
                if child || hides { h } else { main }
            }
            _ => main,
        };
        dbg_log(&format!("menu: from {from:?} autohide {hides} owner {owner:?} main {main:?}"));
        owner
    }
}

/// Windows' colour dialog, starting at `current`; None when cancelled.
unsafe fn choose_color(owner: HWND, current: Option<(u8, u8, u8)>) -> Option<(u8, u8, u8)> {
    use windows::Win32::UI::Controls::Dialogs::{CC_FULLOPEN, CC_RGBINIT, CHOOSECOLORW, ChooseColorW};
    static CUSTOM: std::sync::Mutex<[u32; 16]> = std::sync::Mutex::new([0x00FF_FFFF; 16]);
    let mut custom = CUSTOM.lock().unwrap_or_else(|e| e.into_inner()).map(COLORREF);
    let mut cc = CHOOSECOLORW {
        lStructSize: size_of::<CHOOSECOLORW>() as u32,
        hwndOwner: owner,
        rgbResult: current.map(|(r, g, b)| rgb(r, g, b)).unwrap_or(COLORREF(0x00FF_FFFF)),
        lpCustColors: custom.as_mut_ptr(),
        Flags: CC_FULLOPEN | CC_RGBINIT,
        ..Default::default()
    };
    let ok = unsafe { ChooseColorW(&mut cc) }.as_bool();
    *CUSTOM.lock().unwrap_or_else(|e| e.into_inner()) = custom.map(|c| c.0);
    let c = cc.rgbResult.0;
    ok.then_some(((c & 0xFF) as u8, (c >> 8 & 0xFF) as u8, (c >> 16 & 0xFF) as u8))
}

unsafe fn show_menu(from: Option<HWND>) {
    unsafe {
        let (main, devices, renamed, hidden, vertical) = with_app(|a| {
            a.hide_tip();
            let renamed: HashSet<String> = a.names.keys().cloned().collect();
            (a.main, a.connected(), renamed, a.hidden.clone(), a.vertical)
        })
        .unwrap_or_default();
        let dark = !ui::taskbar_is_light();
        let mut icons = ui::MenuIcons::new(main, dark);
        if let Ok(menu) = CreatePopupMenu() {
            ui::MenuIcons::check_or_icon(menu);
            // The dashboard at once (it opens on the first device; the others are a click away).
            let has_any = !devices.is_empty() || with_app(|a| !a.dashboard_devices().is_empty()).unwrap_or(false);
            let _ = AppendMenuW(menu, MF_STRING | if has_any { MF_ENABLED } else { MF_GRAYED }, ID_DASHBOARD, &windows::core::HSTRING::from(tr("Dashboard...")));
            icons.set(menu, ID_DASHBOARD as u32, false, ui::glyph::DASHBOARD);
            let _ = AppendMenuW(menu, MF_SEPARATOR, 0, windows::core::PCWSTR::null());
            // One submenu per device: dashboard, history, statistics, rename and its warnings.
            settings::append_device_menus(menu, &devices, SETTINGS_KEY, &renamed, &hidden, vertical, &mut icons);
            if !devices.is_empty() {
                let _ = AppendMenuW(menu, MF_SEPARATOR, 0, windows::core::PCWSTR::null());
            }
            let _ = AppendMenuW(menu, MF_STRING, ID_REFRESH_DEVICES, &windows::core::HSTRING::from(tr("Refresh devices")));
            icons.set(menu, ID_REFRESH_DEVICES as u32, false, ui::glyph::SYNC);
            let _ = AppendMenuW(menu, MF_STRING, ID_REFRESH_LEVELS, &windows::core::HSTRING::from(tr("Refresh battery levels")));
            icons.set(menu, ID_REFRESH_LEVELS as u32, false, ui::glyph::REFRESH);
            let _ = AppendMenuW(menu, MF_SEPARATOR, 0, windows::core::PCWSTR::null());
            let check = |on: bool| if on { MF_CHECKED } else { MF_UNCHECKED };
            // Look of the widget: plate behind it, position, and which monitors show it.
            let (choice, offset, background, offset_y, icons_mode, align_left, hide_empty, vertical_bar, compact) =
                with_app(|a| (a.choice.clone(), a.offset, a.background, a.offset_y, a.icons_mode, a.align_left, a.hide_empty, a.vertical, a.compact)).unwrap_or_default();
            let after_icons = with_app(|a| a.after_icons).unwrap_or(false);
            let others: Vec<(String, String)> =
                secondary_taskbars().into_iter().take(ID_MONITOR_GONE - ID_MONITOR_FIRST).map(|b| (monitor_id(b), monitor_label(b))).collect();
            let languages = batteryhub::i18n::available();
            // Widget: how and where the strip looks (#520).
            if let Ok(widget) = CreatePopupMenu() {
                ui::MenuIcons::check_or_icon(widget);
                let _ = AppendMenuW(
                    widget,
                    MF_STRING | check(!hide_empty),
                    ID_SHOW_EMPTY,
                    &windows::core::HSTRING::from(tr("Show the icon when no device is connected")),
                );
                let _ = AppendMenuW(
                    widget,
                    MF_STRING | check(icons_mode),
                    ID_ICONS_MODE,
                    &windows::core::HSTRING::from(tr("Show as notification-area icons (Windows arranges them)")),
                );
                let _ = AppendMenuW(
                    widget,
                    MF_STRING | check(background),
                    ID_BACKGROUND,
                    &windows::core::HSTRING::from(tr("Background behind taskbar text (for translucent taskbars)")),
                );
                // Widget position: next to the clock or next to the taskbar icons (horizontal taskbars).
                if let Ok(sub) = CreatePopupMenu() {
                    let _ = AppendMenuW(sub, MF_STRING, ID_SIDE_RIGHT, &windows::core::HSTRING::from(tr("Right")));
                    let left_ok = if vertical_bar { MF_GRAYED } else { MF_ENABLED };
                    let _ = AppendMenuW(sub, MF_STRING | left_ok, ID_SIDE_ICONS, &windows::core::HSTRING::from(tr("Next to the icons")));
                    let _ = AppendMenuW(sub, MF_STRING | left_ok, ID_SIDE_LEFT, &windows::core::HSTRING::from(tr("Left")));
                    let on = match (align_left && !vertical_bar, after_icons) {
                        (false, _) => ID_SIDE_RIGHT,
                        (true, true) => ID_SIDE_ICONS,
                        (true, false) => ID_SIDE_LEFT,
                    };
                    let _ = CheckMenuRadioItem(sub, ID_SIDE_RIGHT as u32, ID_SIDE_ICONS as u32, on as u32, MF_BYCOMMAND.0);
                    let n = GetMenuItemCount(Some(widget));
                    let _ = AppendMenuW(widget, MF_STRING | MF_POPUP, sub.0 as usize, &windows::core::HSTRING::from(tr("Widget position")));
                    icons.set(widget, n as u32, true, ui::glyph::SETTINGS);
                }
                let _ = AppendMenuW(
                    widget,
                    MF_STRING | check(compact),
                    ID_COMPACT,
                    &windows::core::HSTRING::from(tr("Icons above percentages (narrower)")),
                );
                if let Ok(sub) = CreatePopupMenu() {
                    let mut checked = ID_POSITION_CUSTOM;
                    for (i, px) in POSITION_OFFSETS.iter().enumerate() {
                        let label = if *px == 0 { tr("Next to the notification area") } else { trf("{px} px to the left", &[("px", &px.to_string())]) };
                        let _ = AppendMenuW(sub, MF_STRING, ID_POSITION_FIRST + i, &windows::core::HSTRING::from(label));
                        if *px == offset {
                            checked = ID_POSITION_FIRST + i;
                        }
                    }
                    if checked == ID_POSITION_CUSTOM {
                        // Set with the 10 px steps (or by hand in the registry, TaskbarOffset).
                        let label = trf("Custom: {px} px to the left", &[("px", &offset.to_string())]);
                        let _ = AppendMenuW(sub, MF_STRING | MF_GRAYED, ID_POSITION_CUSTOM, &windows::core::HSTRING::from(label));
                    }
                    let _ = CheckMenuRadioItem(sub, ID_POSITION_FIRST as u32, ID_POSITION_CUSTOM as u32, checked as u32, MF_BYCOMMAND.0);
                    let _ = AppendMenuW(sub, MF_SEPARATOR, 0, windows::core::PCWSTR::null());
                    let step = |on: bool| if on { MF_STRING } else { MF_STRING | MF_GRAYED };
                    let _ = AppendMenuW(sub, step(offset < POSITION_MAX), ID_POSITION_LEFT, &windows::core::HSTRING::from(tr("Move 10 px left")));
                    icons.set(sub, ID_POSITION_LEFT as u32, false, ui::glyph::LEFT);
                    let _ = AppendMenuW(sub, step(offset > 0), ID_POSITION_RIGHT, &windows::core::HSTRING::from(tr("Move 10 px right")));
                    icons.set(sub, ID_POSITION_RIGHT as u32, false, ui::glyph::RIGHT);
                    let n = GetMenuItemCount(Some(widget));
                    // The px steps count from the clock: not used next to the taskbar icons.
                    let grey = if align_left && !vertical_bar { MF_GRAYED } else { MF_ENABLED };
                    let _ = AppendMenuW(widget, MF_STRING | MF_POPUP | grey, sub.0 as usize, &windows::core::HSTRING::from(tr("Position on the taskbar")));
                    icons.set(widget, n as u32, true, ui::glyph::SETTINGS);
                }
                if let Ok(sub) = CreatePopupMenu() {
                    let mut checked = ID_HEIGHT_CUSTOM;
                    for (i, px) in HEIGHT_OFFSETS.iter().enumerate() {
                        let label = match *px {
                            0 => tr("Centred"),
                            p if p < 0 => trf("{px} px up", &[("px", &(-p).to_string())]),
                            p => trf("{px} px down", &[("px", &p.to_string())]),
                        };
                        let _ = AppendMenuW(sub, MF_STRING, ID_HEIGHT_FIRST + i, &windows::core::HSTRING::from(label));
                        if *px == offset_y {
                            checked = ID_HEIGHT_FIRST + i;
                        }
                    }
                    if checked == ID_HEIGHT_CUSTOM {
                        let label = if offset_y < 0 {
                            trf("Custom: {px} px up", &[("px", &(-offset_y).to_string())])
                        } else {
                            trf("Custom: {px} px down", &[("px", &offset_y.to_string())])
                        };
                        let _ = AppendMenuW(sub, MF_STRING | MF_GRAYED, ID_HEIGHT_CUSTOM, &windows::core::HSTRING::from(label));
                    }
                    let _ = CheckMenuRadioItem(sub, ID_HEIGHT_FIRST as u32, ID_HEIGHT_CUSTOM as u32, checked as u32, MF_BYCOMMAND.0);
                    let _ = AppendMenuW(sub, MF_SEPARATOR, 0, windows::core::PCWSTR::null());
                    let step = |on: bool| if on { MF_STRING } else { MF_STRING | MF_GRAYED };
                    let _ = AppendMenuW(sub, step(offset_y > -HEIGHT_MAX), ID_HEIGHT_UP, &windows::core::HSTRING::from(tr("Move 10 px up")));
                    icons.set(sub, ID_HEIGHT_UP as u32, false, ui::glyph::UP);
                    let _ = AppendMenuW(sub, step(offset_y < HEIGHT_MAX), ID_HEIGHT_DOWN, &windows::core::HSTRING::from(tr("Move 10 px down")));
                    icons.set(sub, ID_HEIGHT_DOWN as u32, false, ui::glyph::DOWN);
                    let n = GetMenuItemCount(Some(widget));
                    let _ = AppendMenuW(widget, MF_STRING | MF_POPUP, sub.0 as usize, &windows::core::HSTRING::from(tr("Height on the taskbar")));
                    icons.set(widget, n as u32, true, ui::glyph::SETTINGS);
                }
                // With more than one monitor: all of them, the main one only, or one other monitor only.
                if !others.is_empty()
                    && let Ok(sub) = CreatePopupMenu()
                {
                    let _ = AppendMenuW(sub, MF_STRING, ID_MONITOR_ALL, &windows::core::HSTRING::from(tr("All monitors")));
                    let _ = AppendMenuW(sub, MF_STRING, ID_MONITOR_MAIN, &windows::core::HSTRING::from(tr("Main monitor only")));
                    let ids: Vec<String> = others.iter().map(|o| o.0.clone()).collect();
                    let checked = match choice.as_str() {
                        "all" => ID_MONITOR_ALL,
                        "main" => ID_MONITOR_MAIN,
                        id => find_monitor(&ids, id).map(|i| ID_MONITOR_FIRST + i).unwrap_or(ID_MONITOR_GONE),
                    };
                    for (i, (_, label)) in others.iter().enumerate() {
                        let _ = AppendMenuW(sub, MF_STRING, ID_MONITOR_FIRST + i, &windows::core::HSTRING::from(trf("{monitor} only", &[("monitor", label)])));
                    }
                    if checked == ID_MONITOR_GONE {
                        let _ = AppendMenuW(
                            sub,
                            MF_STRING | MF_GRAYED,
                            ID_MONITOR_GONE,
                            &windows::core::HSTRING::from(tr("Chosen monitor (not connected, shown on main)")),
                        );
                    }
                    let _ = CheckMenuRadioItem(sub, ID_MONITOR_ALL as u32, ID_MONITOR_GONE as u32, checked as u32, MF_BYCOMMAND.0);
                    let n = GetMenuItemCount(Some(widget));
                    let _ = AppendMenuW(widget, MF_STRING | MF_POPUP, sub.0 as usize, &windows::core::HSTRING::from(tr("Show widget on")));
                    icons.set(widget, n as u32, true, ui::glyph::MONITOR);
                }
                let n = GetMenuItemCount(Some(menu));
                let _ = AppendMenuW(menu, MF_STRING | MF_POPUP, widget.0 as usize, &windows::core::HSTRING::from(tr("Widget")));
                icons.set(menu, n as u32, true, ui::glyph::VIEW);
            }
            // Settings: reading, language, autostart and updates.
            if let Ok(settings_menu) = CreatePopupMenu() {
                ui::MenuIcons::check_or_icon(settings_menu);
                // How often the battery levels are read, and whether a device change triggers a read.
                if let Ok(sub) = CreatePopupMenu() {
                    let current = refresh_minutes();
                    for (j, (m, label)) in INTERVALS.iter().enumerate() {
                        let check = if *m == current { MF_CHECKED } else { MF_UNCHECKED };
                        let _ = AppendMenuW(sub, MF_STRING | check, ID_INTERVAL_BASE + j, &windows::core::HSTRING::from(tr(label)));
                    }
                    let n = GetMenuItemCount(Some(settings_menu));
                    let _ = AppendMenuW(settings_menu, MF_STRING | MF_POPUP, sub.0 as usize, &windows::core::HSTRING::from(tr("Refresh battery every")));
                    icons.set(settings_menu, n as u32, true, ui::glyph::HISTORY);
                }
                let on_change = if refresh_on_change() { MF_CHECKED } else { MF_UNCHECKED };
                let _ = AppendMenuW(settings_menu, MF_STRING | on_change, ID_ON_CHANGE, &windows::core::HSTRING::from(tr("Refresh when a device connects or disconnects")));
                let _ = AppendMenuW(settings_menu, MF_SEPARATOR, 0, windows::core::PCWSTR::null());
                // Language: Windows' language, every built-in and user language, and a new one.
                if let Ok(sub) = CreatePopupMenu() {
                    let chosen = language_choice();
                    // Names the language it resolves to: Windows' display language, not its region format.
                    let codes: Vec<String> = languages.iter().map(|(c, _)| c.clone()).collect();
                    let auto = batteryhub::i18n::pick(&batteryhub::i18n::windows_language(), &codes);
                    let auto_name = languages.iter().find(|(c, _)| c.eq_ignore_ascii_case(&auto)).map_or(auto.as_str(), |(_, n)| n.as_str());
                    let auto_label = format!("{} ({auto_name})", tr("Windows language"));
                    let _ = AppendMenuW(sub, MF_STRING | check(chosen.is_empty()), ID_LANG_AUTO, &windows::core::HSTRING::from(auto_label));
                    let _ = AppendMenuW(sub, MF_SEPARATOR, 0, windows::core::PCWSTR::null());
                    for (i, (code, name)) in languages.iter().enumerate().take(ID_LANG_LAST - ID_LANG_FIRST + 1) {
                        let on = chosen.eq_ignore_ascii_case(code);
                        let _ = AppendMenuW(sub, MF_STRING | check(on), ID_LANG_FIRST + i, &windows::core::HSTRING::from(name.as_str()));
                    }
                    let _ = AppendMenuW(sub, MF_SEPARATOR, 0, windows::core::PCWSTR::null());
                    let _ = AppendMenuW(sub, MF_STRING, ID_LANG_NEW, &windows::core::HSTRING::from(tr("Create your own language...")));
                    let _ = AppendMenuW(sub, MF_STRING, ID_LANG_FOLDER, &windows::core::HSTRING::from(tr("Open the languages folder")));
                    let n = GetMenuItemCount(Some(settings_menu));
                    let _ = AppendMenuW(settings_menu, MF_STRING | MF_POPUP, sub.0 as usize, &windows::core::HSTRING::from(tr("Language")));
                    icons.set(settings_menu, n as u32, true, ui::glyph::LANGUAGE);
                }
                let _ = AppendMenuW(settings_menu, MF_SEPARATOR, 0, windows::core::PCWSTR::null());
                let _ = AppendMenuW(
                    settings_menu,
                    MF_STRING | check(ui::autostart_enabled(autostart_name())),
                    ID_AUTOSTART,
                    &windows::core::HSTRING::from(tr("Automatically start with Windows")),
                );
                let _ = AppendMenuW(settings_menu, MF_STRING | check(auto_update()), ID_AUTO_UPDATE, &windows::core::HSTRING::from(tr("Automatically check for updates")));
                let _ = AppendMenuW(
                    settings_menu,
                    MF_STRING | check(silent_install()) | if auto_update() { MF_ENABLED } else { MF_GRAYED },
                    ID_SILENT_UPDATE,
                    &windows::core::HSTRING::from(tr("Install updates silently")),
                );
                let n = GetMenuItemCount(Some(menu));
                let _ = AppendMenuW(menu, MF_STRING | MF_POPUP, settings_menu.0 as usize, &windows::core::HSTRING::from(tr("Settings")));
                icons.set(menu, n as u32, true, ui::glyph::SETTINGS);
            }
            // Help: updates, other versions, device requests, the project's pages and the latest
            // releases (their pages; loaded in the background).
            if let Ok(sub) = CreatePopupMenu() {
                ui::MenuIcons::check_or_icon(sub);
                let busy = UPDATE_BUSY.load(std::sync::atomic::Ordering::Relaxed);
                let label = if busy { tr("Checking for updates...") } else { tr("Check for updates...") };
                let _ = AppendMenuW(sub, MF_STRING | if busy { MF_GRAYED } else { MF_ENABLED }, ID_CHECK_UPDATES, &windows::core::HSTRING::from(label));
                icons.set(sub, ID_CHECK_UPDATES as u32, false, ui::glyph::DOWNLOAD);
                let _ = AppendMenuW(sub, MF_STRING, ID_VERSIONS, &windows::core::HSTRING::from(tr("Install another version...")));
                icons.set(sub, ID_VERSIONS as u32, false, ui::glyph::HISTORY);
                let _ = AppendMenuW(sub, MF_STRING, ID_REQUEST, &windows::core::HSTRING::from(tr("Request support for a device...")));
                icons.set(sub, ID_REQUEST as u32, false, ui::glyph::MAIL);
                let _ = AppendMenuW(sub, MF_SEPARATOR, 0, windows::core::PCWSTR::null());
                let _ = AppendMenuW(sub, MF_STRING, ID_HELP_GITHUB, &windows::core::HSTRING::from(tr("Go to the GitHub page")));
                icons.set(sub, ID_HELP_GITHUB as u32, false, ui::glyph::INFO);
                let _ = AppendMenuW(sub, MF_STRING, ID_HELP_DISCORD, &windows::core::HSTRING::from(tr("Join the Discord server")));
                let _ = AppendMenuW(sub, MF_STRING, ID_HELP_FREE, &windows::core::HSTRING::from(format!("{}  ♥", tr("BatteryHub is free and will stay free"))));
                let _ = AppendMenuW(sub, MF_SEPARATOR, 0, windows::core::PCWSTR::null());
                let _ = AppendMenuW(sub, MF_STRING | MF_GRAYED, 0, &windows::core::HSTRING::from(tr("Recent updates")));
                let releases = recent_releases();
                if releases.is_empty() {
                    let _ = AppendMenuW(sub, MF_STRING | MF_GRAYED, 0, &windows::core::HSTRING::from(tr("Loading...")));
                }
                for (i, (version, _)) in releases.iter().enumerate().take(HELP_RELEASES) {
                    let label = if *version == batteryhub::install::VERSION { format!("v{version}  ✓") } else { format!("v{version}") };
                    let _ = AppendMenuW(sub, MF_STRING, ID_HELP_RELEASE_FIRST + i, &windows::core::HSTRING::from(label));
                }
                let n = GetMenuItemCount(Some(menu));
                let _ = AppendMenuW(menu, MF_STRING | MF_POPUP, sub.0 as usize, &windows::core::HSTRING::from(tr("Help")));
                icons.set(menu, n as u32, true, ui::glyph::INFO);
            }
            let _ = AppendMenuW(menu, MF_SEPARATOR, 0, windows::core::PCWSTR::null());
            let _ = AppendMenuW(menu, MF_STRING, ID_EXIT, &windows::core::HSTRING::from(tr("Exit")));
            icons.set(menu, ID_EXIT as u32, false, ui::glyph::EXIT);
            let mut pt = POINT::default();
            let _ = GetCursorPos(&mut pt);
            // With an auto-hiding taskbar the menu belongs to the strip under the cursor (a child of
            // the taskbar): the taskbar then stays the active window and stays shown while the menu
            // is open. Owned by our own window instead, the taskbar hid as soon as the mouse left it
            // for the menu, and took the menu with it.
            let mut owner = menu_owner(main, from);
            // The window to activate: the taskbar itself for the strip inside it (a child window can't
            // be the foreground window). With nothing active, StartAllBack's auto-hide hid the
            // taskbar as soon as the mouse left it for the menu and activated its own edge window,
            // which closed the menu.
            let root = GetAncestor(owner, GA_ROOT);
            let active = if root.0.is_null() { owner } else { root };
            let _ = SetForegroundWindow(active);
            if active != main && GetForegroundWindow() != active {
                // Not allowed to activate the taskbar: our own window then, so the menu stays open
                // even if the taskbar hides.
                owner = main;
                let _ = SetForegroundWindow(main);
            }
            dbg_log(&format!("menu: active {active:?} foreground {:?} owner {owner:?}", GetForegroundWindow()));
            // Menu colours follow the taskbar: dark on a dark taskbar, light on a light one.
            ui::set_menu_theme(owner, dark);
            // Drawn like Windows 11's own context menus (rows, icons, highlight, chevrons).
            let _modern = ui::ModernMenu::apply(menu, &icons, owner, dark);
            MENU_OPEN.store(true, std::sync::atomic::Ordering::Relaxed);
            let cmd = TrackPopupMenu(menu, TPM_RETURNCMD | TPM_RIGHTBUTTON | TPM_BOTTOMALIGN, pt.x, pt.y, None, owner, None);
            MENU_OPEN.store(false, std::sync::atomic::Ordering::Relaxed);
            // Whatever the mouse crossed while the menu was open does not open the card.
            with_app(|a| a.hide_tip());
            let _ = PostMessageW(Some(main), WM_NULL, WPARAM(0), LPARAM(0));
            let _ = DestroyMenu(menu);
            match cmd.0 as usize {
                ID_EXIT => {
                    let _ = DestroyWindow(main);
                }
                ID_REFRESH_DEVICES => {
                    with_app(|a| a.manual_refresh(true));
                }
                ID_DASHBOARD => {
                    if let Some((first, _)) = with_app(|a| a.dashboard_devices().into_iter().next()).flatten() {
                        device_action(&first, settings::DeviceAction::Dashboard(0), &devices);
                    }
                }
                ID_REFRESH_LEVELS => {
                    with_app(|a| a.manual_refresh(false));
                }
                ID_CHECK_UPDATES => check_for_updates(main, false),
                ID_VERSIONS => open_version_list(main),
                ID_ICONS_MODE => {
                    let on = with_app(|a| {
                        a.icons_mode = !a.icons_mode;
                        save_dword("NotificationIcons", a.icons_mode as u32);
                        if a.icons_mode {
                            a.set_fallback(true);
                        } else {
                            a.set_fallback(false);
                            a.tick();
                        }
                        a.icons_mode
                    })
                    .unwrap_or(false);
                    if on {
                        message(
                            main,
                            &tr(
                                "BatteryHub now shows one notification-area icon per device, with its level drawn in the icon.\n\nWindows places these icons like any other: drag them to reorder, or move them in or out of the hidden-icons area. If you don't see them, open Settings > Personalization > Taskbar > Other system tray icons and turn BatteryHub on.",
                            ),
                            MB_OK | MB_ICONINFORMATION,
                        );
                    }
                }
                ID_SIDE_RIGHT | ID_SIDE_LEFT | ID_SIDE_ICONS => {
                    let side = match cmd.0 as usize {
                        ID_SIDE_LEFT => 1,
                        ID_SIDE_ICONS => 2,
                        _ => 0,
                    };
                    save_dword("WidgetLeft", side);
                    with_app(|a| {
                        a.align_left = side != 0;
                        a.after_icons = side == 2;
                        a.last_place = Default::default();
                        a.place();
                        a.sync_mirrors();
                    });
                }
                ID_SHOW_EMPTY => {
                    with_app(|a| {
                        a.hide_empty = !a.hide_empty;
                        save_dword("HideWhenEmpty", a.hide_empty as u32);
                        a.paint();
                        a.sync_app_icon();
                    });
                }
                ID_HELP_GITHUB => open_url(&format!("https://github.com/{}", batteryhub::update::REPO)),
                ID_HELP_DISCORD => open_url(DISCORD_URL),
                ID_HELP_FREE => open_url(SUPPORT_URL),
                id if (ID_HELP_RELEASE_FIRST..ID_HELP_RELEASE_FIRST + HELP_RELEASES).contains(&id) => {
                    if let Some((_, url)) = recent_releases().get(id - ID_HELP_RELEASE_FIRST) {
                        open_url(url);
                    }
                }
                ID_COMPACT => {
                    with_app(|a| {
                        a.compact = !a.compact;
                        save_dword("CompactWidget", a.compact as u32);
                        a.paint();
                        a.tick();
                        // The new layout pops in on every taskbar alike (the copies on other monitors
                        // too, which otherwise just switched).
                        let mut strips: Vec<HWND> = a.mirrors.iter().map(|m| m.1).collect();
                        strips.push(a.strip);
                        for st in strips {
                            if !st.0.is_null() && IsWindowVisible(st).as_bool() {
                                a.start_pop(st, false);
                            }
                        }
                    });
                }
                ID_BACKGROUND => {
                    with_app(|a| {
                        a.background = !a.background;
                        save_dword("WidgetBackground", a.background as u32);
                        a.paint();
                    });
                }
                id if (ID_POSITION_FIRST..ID_POSITION_FIRST + POSITION_OFFSETS.len()).contains(&id) => set_offset(POSITION_OFFSETS[id - ID_POSITION_FIRST]),
                ID_POSITION_LEFT => set_offset((offset + 10).min(POSITION_MAX)),
                ID_POSITION_RIGHT => set_offset(offset.saturating_sub(10)),
                id if (ID_HEIGHT_FIRST..ID_HEIGHT_FIRST + HEIGHT_OFFSETS.len()).contains(&id) => set_offset_y(HEIGHT_OFFSETS[id - ID_HEIGHT_FIRST]),
                ID_HEIGHT_UP => set_offset_y((offset_y - 10).max(-HEIGHT_MAX)),
                ID_HEIGHT_DOWN => set_offset_y((offset_y + 10).min(HEIGHT_MAX)),
                id if id == ID_MONITOR_ALL || id == ID_MONITOR_MAIN || (ID_MONITOR_FIRST..ID_MONITOR_FIRST + others.len()).contains(&id) => {
                    let v = match id {
                        ID_MONITOR_ALL => "all".to_string(),
                        ID_MONITOR_MAIN => "main".to_string(),
                        i => others[i - ID_MONITOR_FIRST].0.clone(),
                    };
                    batteryhub::util::reg_set_string(SETTINGS_KEY, "WidgetMonitor", &v);
                    with_app(|a| {
                        a.choice = v;
                        a.sync_mirrors();
                    });
                }
                ID_AUTOSTART => {
                    let on = !ui::autostart_enabled(autostart_name());
                    ui::set_autostart(autostart_name(), on);
                    if on {
                        // A "disabled" state left in Task Manager would keep it from starting.
                        batteryhub::util::reg_delete_value(batteryhub::install::STARTUP_APPROVED_KEY, autostart_name());
                    }
                }
                ID_AUTO_UPDATE => {
                    let on = !auto_update();
                    save_dword("AutoCheckUpdates", on as u32);
                    if on {
                        message(
                            main,
                            &tr(
                                "Automatic update check is on.\n\nBatteryHub looks for a new version only when it starts (at sign-in or when you start it), not while it runs. When there is one, it asks you whether to update (or, with \"Install updates silently\", installs it in the background).",
                            ),
                            MB_OK | MB_ICONINFORMATION,
                        );
                    }
                }
                ID_SILENT_UPDATE => {
                    let on = !silent_install();
                    save_dword("SilentUpdates", on as u32);
                    if on {
                        message(
                            main,
                            &tr(
                                "Silent updates are on.\n\nWhen BatteryHub starts and finds a new version, it downloads it from GitHub, checks its SHA-256 checksum and installs it in the background, without asking and without showing anything. Your settings and autostart are kept.",
                            ),
                            MB_OK | MB_ICONINFORMATION,
                        );
                    }
                }
                ID_REQUEST => batteryhub::report_window::show(),
                ID_LANG_AUTO => set_language(""),
                id if (ID_LANG_FIRST..=ID_LANG_LAST).contains(&id) => {
                    if let Some((code, _)) = languages.get(id - ID_LANG_FIRST) {
                        set_language(code);
                    }
                }
                ID_LANG_NEW => match batteryhub::i18n::create_template() {
                    Ok(path) => {
                        let _ = std::process::Command::new("notepad.exe").arg(&path).spawn();
                        message(
                            main,
                            &trf(
                                "A new language file was created:\n{path}\n\nIt lists every text of BatteryHub. Write the translation after the equals sign on each line, set @code and @name at the top, save it, and then pick it in the Language menu. Texts you leave out stay in English.",
                                &[("path", &path.display().to_string())],
                            ),
                            MB_OK | MB_ICONINFORMATION,
                        );
                    }
                    Err(e) => {
                        message(main, &trf("Could not create the language file:\n{error}", &[("error", &e.to_string())]), MB_OK | MB_ICONWARNING);
                    }
                },
                ID_LANG_FOLDER => {
                    let dir = batteryhub::i18n::user_dir();
                    let _ = std::fs::create_dir_all(&dir);
                    let _ = std::process::Command::new("explorer.exe").arg(&dir).spawn();
                }
                ID_ON_CHANGE => {
                    let on = !refresh_on_change();
                    save_dword("RefreshOnDeviceChange", on as u32);
                    ON_CHANGE.store(on as u8, std::sync::atomic::Ordering::Relaxed);
                }
                id if (ID_INTERVAL_BASE..ID_INTERVAL_BASE + INTERVALS.len()).contains(&id) => {
                    let minutes = INTERVALS[id - ID_INTERVAL_BASE].0;
                    save_dword("RefreshMinutes", minutes);
                    SetTimer(Some(main), TIMER_POLL, minutes * 60_000, None);
                }
                id => {
                    if let Some((dev, action)) = settings::decode_menu_id(id)
                        && let Some(d) = devices.get(dev)
                    {
                        device_action(d, action, &devices);
                    }
                }
            }
        }
    }
}

/// Gap left of the notification area (TaskbarOffset, px).
fn set_offset(px: u32) {
    if px == 0 {
        batteryhub::util::reg_delete_value(SETTINGS_KEY, "TaskbarOffset");
    } else {
        save_dword("TaskbarOffset", px);
    }
    with_app(|a| {
        a.offset = px;
        a.last_place = Default::default();
        a.place();
        a.sync_mirrors();
    });
}

/// Up / down shift of the widget (TaskbarOffsetY, px, + = down).
/// Progress of a glide that started at `t0`, eased out (0 to 1).
fn glide_ease(t0: Instant) -> f32 {
    let p = (t0.elapsed().as_secs_f32() * 1000.0 / GLIDE_MS).min(1.0);
    1.0 - (1.0 - p).powi(3)
}

fn set_offset_y(px: i32) {
    if px == 0 {
        batteryhub::util::reg_delete_value(SETTINGS_KEY, "TaskbarOffsetY");
    } else {
        save_dword("TaskbarOffsetY", px as u32);
    }
    with_app(|a| {
        if a.offset_y != px {
            a.y_glide = Some((a.shown_offset_y(), Instant::now()));
            unsafe {
                SetTimer(Some(a.main), TIMER_GLIDE, 15, None);
            }
        }
        a.offset_y = px;
        a.paint();
        a.sync_mirrors();
    });
}

/// "Reset measurements": asks first, then deletes the device's history.
const BATTERY_ONLY_QUESTION: &str = n_(
    "Use Battery only for {name}?\n\nIts battery history and statistics are deleted, and from now on nothing is recorded or worked out for it: only its level is shown. This cannot be undone."
);

fn confirm_reset(main: HWND, d: &DeviceStatus) {
    let text = batteryhub::dashboard::reset_question(&d.name);
    let answer = unsafe {
        MessageBoxW(
            Some(main),
            &windows::core::HSTRING::from(text),
            &windows::core::HSTRING::from(tr("Reset measurements")),
            MB_YESNO | MB_ICONWARNING | MB_DEFBUTTON2 | MB_SETFOREGROUND,
        )
    };
    if answer == IDYES {
        with_app(|a| a.reset_history(&d.key));
    }
}

/// An item of a device's submenu was chosen.
fn device_action(d: &DeviceStatus, action: settings::DeviceAction, devices: &[DeviceStatus]) {
    use settings::DeviceAction;
    let reported = with_app(|a| a.devices.get(&d.key).map(|t| t.reported.clone())).flatten().unwrap_or_else(|| d.name.clone());
    match action {
        DeviceAction::Dashboard(tab) => {
            // The dashboard reads the history file: write the latest readings first.
            with_app(|a| a.save_history_now());
            batteryhub::dashboard::open(d, &reported, tab);
        }
        DeviceAction::Rename => batteryhub::rename::open(d, &reported),
        DeviceAction::ResetName => {
            settings::set_name(SETTINGS_KEY, &d.key, None);
            with_app(|a| a.reload_names());
        }
        DeviceAction::ToggleShown => {
            with_app(|a| {
                let hide = !a.hidden.contains(&d.key);
                settings::set_hidden(SETTINGS_KEY, &d.key, hide);
                a.hidden = settings::hidden(SETTINGS_KEY);
                a.hide_tip();
                a.card_cache.clear();
                a.paint();
            });
        }
        DeviceAction::Hover(m) => {
            settings::set_hover_mode(SETTINGS_KEY, &d.key, m);
            with_app(|a| a.hide_tip());
        }
        DeviceAction::ToggleCardChart => {
            settings::set_card_chart(SETTINGS_KEY, &d.key, !settings::card_chart(SETTINGS_KEY, &d.key));
            with_app(|a| a.card_cache.clear());
        }
        DeviceAction::ToggleCardTime => {
            settings::set_card_time(SETTINGS_KEY, &d.key, !settings::card_time(SETTINGS_KEY, &d.key));
            with_app(|a| a.card_cache.clear());
        }
        DeviceAction::ToggleBatteryOnly => {
            let on = !settings::battery_only(SETTINGS_KEY, &d.key);
            // Turning it on deletes what was measured: asked first.
            if on {
                let Some(main) = with_app(|a| a.main) else { return };
                let answer = unsafe {
                    MessageBoxW(
                        Some(main),
                        &windows::core::HSTRING::from(trf(BATTERY_ONLY_QUESTION, &[("name", &d.name)])),
                        &windows::core::HSTRING::from(tr("Battery only")),
                        MB_YESNO | MB_ICONWARNING | MB_DEFBUTTON2 | MB_SETFOREGROUND,
                    )
                };
                if answer != IDYES {
                    return;
                }
            }
            settings::set_battery_only(SETTINGS_KEY, &d.key, on);
            with_app(|a| {
                if on {
                    a.reset_history(&d.key);
                }
                a.card_cache.clear();
            });
        }
        DeviceAction::ToggleRiseCharging => {
            settings::set_rise_charging(SETTINGS_KEY, &d.key, !settings::rise_charging(SETTINGS_KEY, &d.key));
            with_app(|a| {
                a.rising.remove(&d.key);
                a.card_cache.clear();
            });
        }
        DeviceAction::ToggleWarn5 => {
            settings::set_warn_critical(SETTINGS_KEY, &d.key, !settings::warn_critical(SETTINGS_KEY, &d.key));
        }
        DeviceAction::IconColor(c) => {
            settings::set_icon_color(SETTINGS_KEY, &d.key, c);
            with_app(|a| {
                a.card_cache.clear();
                a.paint();
            });
        }
        DeviceAction::CustomColor => {
            let Some(main) = with_app(|a| a.main) else { return };
            let current = settings::icon_rgb(settings::icon_color(SETTINGS_KEY, &d.key), d.vid);
            if let Some((r, g, b)) = unsafe { choose_color(main, current) } {
                settings::set_icon_color(SETTINGS_KEY, &d.key, settings::IconColor::Rgb(r, g, b));
                with_app(|a| {
                    a.card_cache.clear();
                    a.paint();
                });
            }
        }
        DeviceAction::ToggleRedIcon => {
            settings::set_red_icon(SETTINGS_KEY, &d.key, !settings::red_icon(SETTINGS_KEY, &d.key));
            with_app(|a| {
                a.card_cache.clear();
                a.paint();
            });
        }
        DeviceAction::Threshold(level) => {
            settings::set_threshold(SETTINGS_KEY, &d.key, level);
            with_app(|a| {
                a.card_cache.clear();
                a.paint();
            });
        }
        DeviceAction::Move(on) => {
            let Some(i) = devices.iter().position(|x| x.key == d.key) else { return };
            let j = if on { i + 1 } else { i.wrapping_sub(1) };
            if let Some(other) = devices.get(j) {
                with_app(|a| a.swap_devices(&d.key, &other.key));
            }
        }
        DeviceAction::ResetHistory => {
            if let Some(main) = with_app(|a| a.main) {
                confirm_reset(main, d);
            }
        }
    }
}

// ---- window procedures -------------------------------------------------------------------------

/// Windows of the taskbar itself (Windows 10 / 11 / ExplorerPatcher), never treated as widgets.
const TASKBAR_PARTS: [&str; 16] = [
    "Start",
    "TrayNotifyWnd",
    "ReBarWindow32",
    "MSTaskSwWClass",
    "MSTaskListWClass",
    "TrayDummySearchControl",
    "Windows.UI.Composition.DesktopWindowContentBridge",
    "Windows.UI.Core.CoreWindow",
    "Windows.UI.Input.InputSite.WindowClass",
    "WorkerW",
    "ClockButton",
    "TrayClockWClass",
    "TrayButton",
    "TrayShowDesktopButtonWClass",
    "SIBTrayButton",
    "BatteryHub.Taskbar.Strip",
];

/// x ranges (client coordinates of `bar`) of other programs' windows embedded in the taskbar,
/// such as network or CPU meters: direct child windows that are not part of the taskbar.
/// Spans in `bar`'s client x as screen x.
fn screen_spans(bar: HWND, spans: &[(i32, i32)]) -> Vec<(i32, i32)> {
    let mut p = POINT::default();
    unsafe {
        let _ = ClientToScreen(bar, &mut p);
    }
    spans.iter().map(|&(a, b)| (a + p.x, b + p.x)).collect()
}

fn foreign_widgets(bar: HWND) -> Vec<(i32, i32)> {
    let mut out = Vec::new();
    unsafe {
        let mut br = RECT::default();
        let _ = GetClientRect(bar, &mut br);
        let mut after: Option<HWND> = None;
        while let Ok(h) = FindWindowExW(Some(bar), after, None, None) {
            if h.0.is_null() {
                break;
            }
            after = Some(h);
            if !IsWindowVisible(h).as_bool() {
                continue;
            }
            let mut cls = [0u16; 128];
            let n = GetClassNameW(h, &mut cls);
            let name = String::from_utf16_lossy(&cls[..n.max(0) as usize]);
            if TASKBAR_PARTS.contains(&name.as_str()) {
                continue;
            }
            let mut r = RECT::default();
            let _ = GetWindowRect(h, &mut r);
            let mut tl = POINT { x: r.left, y: r.top };
            let _ = ScreenToClient(bar, &mut tl);
            let w = r.right - r.left;
            // Skip empty and taskbar-wide windows (hosts, not widgets).
            if w <= 0 || r.bottom <= r.top || w * 2 > br.right - br.left {
                continue;
            }
            out.push((tl.x, tl.x + w));
        }
    }
    out
}

/// Moves a strip of width `w` that would start at `left` further left until it overlaps none
/// of the other widgets, keeping `gap` px between them.
fn avoid_widgets(bar: HWND, left: i32, w: i32, gap: i32) -> i32 {
    let others = foreign_widgets(bar);
    shift_left_of(left, w, gap, &others)
}

/// Placed pieces (x, y, shown), total height, device rows (from, to, device).
type ColumnLayout = (Vec<(i32, i32, bool)>, i32, Vec<(i32, i32, usize)>);

/// Lays out strip pieces (device, width, height) as a column `w` wide: per device its first
/// piece (the icon) on one line and the rest (level, bolt) centred on the next; a piece that does
/// not fit beside the level is left out. Pieces of no device get a line of their own. Returns
/// (x, y, shown) per piece, the total height, and the y range of each device (from, to, device).
fn column_layout(pieces: &[(Option<usize>, i32, i32)], w: i32, pad: i32, line_gap: i32, dev_gap: i32, piece_gap: i32) -> ColumnLayout {
    let mut out = vec![(0, 0, false); pieces.len()];
    let mut hits: Vec<(i32, i32, usize)> = Vec::new();
    let mut y = pad;
    let mut i = 0;
    while i < pieces.len() {
        let dev = pieces[i].0;
        let mut j = i + 1;
        while dev.is_some() && j < pieces.len() && pieces[j].0 == dev {
            j += 1;
        }
        let start = y;
        // First line: the icon.
        let (_, iw, ih) = pieces[i];
        out[i] = ((w - iw) / 2, y, true);
        y += ih;
        // Second line: the level and what fits beside it.
        if j > i + 1 {
            y += line_gap;
            let mut line_w = 0;
            let mut last = i + 1;
            #[allow(clippy::needless_range_loop)]
            for k in i + 1..j {
                let add = pieces[k].1 + if k > i + 1 { piece_gap } else { 0 };
                if k > i + 1 && line_w + add > w - 2 {
                    break;
                }
                line_w += add;
                last = k;
            }
            let line_h = (i + 1..=last).map(|k| pieces[k].2).max().unwrap_or(0);
            let mut x = (w - line_w) / 2;
            for k in i + 1..=last {
                out[k] = (x, y + (line_h - pieces[k].2) / 2, true);
                x += pieces[k].1 + piece_gap;
            }
            y += line_h;
        }
        if let Some(d) = dev {
            hits.push((start - dev_gap / 2, y + dev_gap / 2, d));
        }
        i = j;
        if i < pieces.len() {
            y += dev_gap;
        }
    }
    let h = y + pad;
    if let Some(first) = hits.first_mut() {
        first.0 = 0;
    }
    if let Some(last) = hits.last_mut() {
        last.1 = h;
    }
    (out, h, hits)
}

fn shift_left_of(mut left: i32, w: i32, gap: i32, others: &[(i32, i32)]) -> i32 {
    for _ in 0..16 {
        match others.iter().filter(|(a, b)| *a < left + w && *b > left).map(|(a, _)| *a).min() {
            Some(a) => left = a - gap - w,
            None => break,
        }
    }
    left
}

/// The hover card's animation: what it shows, where it ends up, and how far it slides.
#[derive(Default)]
struct CardAnim {
    /// Start of the running fade, None when it is at rest.
    at: Option<Instant>,
    /// Fading in (true) or out.
    showing: bool,
    /// On screen (or fading out).
    visible: bool,
    x: i32,
    y: i32,
    slide: i32,
    content: Option<Rc<CardContent>>,
    /// While switching devices: where the background started (x, width) and the previous card's
    /// content, fading out as the background glides to the new card.
    prev: Option<(i32, i32, Rc<CardContent>)>,
    /// Background drawn in the last frame (screen x, width): the next switch starts there.
    drawn: (i32, i32),
    /// Vertical taskbar: the card sits beside it, switches glide up / down (from `prev_y`, the
    /// screen y drawn when the switch started) and it slides in sideways.
    vertical: bool,
    prev_y: i32,
    drawn_y: i32,
    /// Height drawn when the switch started, and in the last frame: cards of different height
    /// (earbuds have two charts) glide from one height to the other.
    prev_h: i32,
    drawn_h: i32,
    bg: COLORREF,
    border: COLORREF,
    radius: i32,
    /// DPI scale of the monitor the card is on.
    scale: f32,
}

/// The card's bitmap and memory DC, kept while the card is open.
struct Surface {
    dc: HDC,
    bmp: HBITMAP,
    old: HGDIOBJ,
    bits: *mut u32,
    w: i32,
    h: i32,
}

impl Surface {
    fn new(w: i32, h: i32) -> Option<Self> {
        unsafe {
            let dc = CreateCompatibleDC(None);
            let bmi = BITMAPINFO {
                bmiHeader: BITMAPINFOHEADER {
                    biSize: size_of::<BITMAPINFOHEADER>() as u32,
                    biWidth: w,
                    biHeight: -h,
                    biPlanes: 1,
                    biBitCount: 32,
                    biCompression: BI_RGB.0,
                    ..Default::default()
                },
                ..Default::default()
            };
            let mut bits: *mut c_void = std::ptr::null_mut();
            match CreateDIBSection(Some(dc), &bmi, DIB_RGB_COLORS, &mut bits, None, 0) {
                Ok(bmp) if !bits.is_null() => {
                    let old = SelectObject(dc, HGDIOBJ(bmp.0));
                    Some(Surface { dc, bmp, old, bits: bits.cast(), w, h })
                }
                _ => {
                    let _ = DeleteDC(dc);
                    None
                }
            }
        }
    }

    fn pixels(&mut self) -> &mut [u32] {
        unsafe { std::slice::from_raw_parts_mut(self.bits, (self.w * self.h) as usize) }
    }

    /// Shows the top-left `size` of the bitmap at `pt` (screen coordinates) with opacity `alpha`.
    fn present(&self, hwnd: HWND, pt: POINT, size: SIZE, alpha: u8) {
        unsafe {
            let _ = GdiFlush();
            let src = POINT::default();
            let bf = BLENDFUNCTION { BlendOp: AC_SRC_OVER as u8, BlendFlags: 0, SourceConstantAlpha: alpha, AlphaFormat: AC_SRC_ALPHA as u8 };
            let _ = UpdateLayeredWindow(hwnd, None, Some(&pt), Some(&size), Some(self.dc), Some(&src), COLORREF(0), Some(&bf), ULW_ALPHA);
        }
    }
}

impl Drop for Surface {
    fn drop(&mut self) {
        unsafe {
            SelectObject(self.dc, self.old);
            let _ = DeleteObject(HGDIOBJ(self.bmp.0));
            let _ = DeleteDC(self.dc);
        }
    }
}

const CARD_CLASS: windows::core::PCWSTR = w!("BatteryHub.Taskbar.Card");

/// The hover card: a layered, topmost popup owned by the main window. It takes the mouse (to pick
/// an hour on its chart) but is never activated.
fn create_card(owner: HWND) -> HWND {
    unsafe {
        let hinst = GetModuleHandleW(None).unwrap_or_default();
        CreateWindowExW(
            WS_EX_LAYERED | WS_EX_TOOLWINDOW | WS_EX_TOPMOST | WS_EX_NOACTIVATE,
            CARD_CLASS,
            w!(""),
            WS_POPUP,
            0,
            0,
            1,
            1,
            Some(owner),
            None,
            Some(hinst.into()),
            None,
        )
        .unwrap_or_default()
    }
}

extern "system" fn card_proc(hwnd: HWND, msg: u32, wp: WPARAM, lp: LPARAM) -> LRESULT {
    unsafe {
        match msg {
            WM_MOUSEMOVE => {
                with_app(|a| a.card_mouse());
                LRESULT(0)
            }
            WM_RBUTTONUP => {
                show_menu(None);
                LRESULT(0)
            }
            WM_MOUSEACTIVATE => LRESULT(MA_NOACTIVATE as isize),
            _ => DefWindowProcW(hwnd, msg, wp, lp),
        }
    }
}

extern "system" fn strip_proc(hwnd: HWND, msg: u32, wp: WPARAM, lp: LPARAM) -> LRESULT {
    unsafe {
        match msg {
            // The context menu is owned by the strip with an auto-hiding taskbar (menu_owner).
            WM_MEASUREITEM if ui::measure_menu_item(lp) => LRESULT(1),
            WM_DRAWITEM if ui::draw_menu_item(lp) => LRESULT(1),
            WM_MOUSEMOVE => {
                with_app(|a| a.hover(hwnd, (lp.0 & 0xFFFF) as i16 as i32, ((lp.0 >> 16) & 0xFFFF) as i16 as i32));
                LRESULT(0)
            }
            WM_MOUSELEAVE => {
                // Re-ordering or redrawing the strip can report a leave while the mouse is still
                // on it: then keep the card and track again, otherwise close it.
                let mut pt = POINT::default();
                let mut rc = RECT::default();
                let still_over = GetCursorPos(&mut pt).is_ok() && GetWindowRect(hwnd, &mut rc).is_ok() && PtInRect(&rc, pt).as_bool();
                if still_over {
                    with_app(|a| {
                        a.tracking = false;
                        let mut c = pt;
                        let _ = ScreenToClient(hwnd, &mut c);
                        a.tip_for = None;
                        a.hover(hwnd, c.x, c.y);
                    });
                } else {
                    with_app(|a| a.leave_strip());
                }
                LRESULT(0)
            }
            WM_RBUTTONUP => {
                with_app(|a| a.end_drag());
                show_menu(Some(hwnd));
                LRESULT(0)
            }
            WM_LBUTTONDOWN => {
                with_app(|a| a.start_drag(hwnd, (lp.0 & 0xFFFF) as i16 as i32, ((lp.0 >> 16) & 0xFFFF) as i16 as i32));
                LRESULT(0)
            }
            WM_LBUTTONUP => {
                with_app(|a| a.end_drag());
                LRESULT(0)
            }
            WM_CAPTURECHANGED => {
                with_app(|a| a.drag = None);
                LRESULT(0)
            }
            WM_MOUSEACTIVATE => LRESULT(MA_NOACTIVATE as isize),
            _ => DefWindowProcW(hwnd, msg, wp, lp),
        }
    }
}

extern "system" fn main_proc(hwnd: HWND, msg: u32, wp: WPARAM, lp: LPARAM) -> LRESULT {
    unsafe {
        match msg {
            WM_POLL_DONE => {
                let devices = ui::take_result(lp);
                with_app(|a| a.on_result(devices));
                // Hand pages used only during the read (enumeration, Bluetooth, fonts) back to
                // Windows until the next read, instead of keeping them resident for a minute or more.
                trim_memory();
                LRESULT(0)
            }
            WM_TIMER if wp.0 == TIMER_CARD => {
                // Animation frames: no memory trim here (it runs ~60 times a second for 0.15 s).
                with_app(|a| a.card_step());
                LRESULT(0)
            }
            WM_TIMER => {
                with_app(|a| match wp.0 {
                    TIMER_POLL => a.start_poll(),
                    TIMER_DEVCHANGE => {
                        let _ = KillTimer(Some(hwnd), TIMER_DEVCHANGE);
                        a.devchange = true;
                        a.start_poll();
                    }
                    TIMER_QUICK => a.start_quick(),
                    TIMER_NOTIFY => a.end_notify(),
                    TIMER_AWAY => a.away_step(),
                    TIMER_SLIDE => a.paint(),
                    TIMER_MIRROR_IN => a.mirror_in_step(),
                    TIMER_GLIDE => a.glide_step(),
                    TIMER_LEFT_PROBE => {
                        a.left_probes = a.left_probes.saturating_sub(1);
                        if a.left_probes == 0 {
                            let _ = KillTimer(Some(hwnd), TIMER_LEFT_PROBE);
                        }
                        batteryhub::tray_probe::left_refresh_soon();
                        a.place();
                        for i in 0..a.mirrors.len() {
                            a.place_mirror_at(i);
                        }
                    }
                    TIMER_UPDATED => {
                        let _ = KillTimer(Some(hwnd), TIMER_UPDATED);
                        if let Some(old) = a.updated_from.take() {
                            let text = trf(
                                "Update finished.\n\nBatteryHub was updated:  {old}  ->  {new}\n\nYour settings and autostart were kept.",
                                &[("old", &batteryhub::install::label_of(&old)), ("new", &batteryhub::install::version_label())],
                            );
                            post_from_thread(hwnd, WM_SHOW_UPDATED, move || text);
                        }
                    }
                    TIMER_AUTO_UPDATE => {
                        let _ = KillTimer(Some(hwnd), TIMER_AUTO_UPDATE);
                        check_for_updates(hwnd, true);
                    }
                    TIMER_BTWATCH => {
                        // Bluetooth connect / disconnect does not add or remove device nodes, so
                        // Windows sends no device-change message for it: compare a signature.
                        if refresh_on_change() {
                            let sig = batteryhub::drivers::bluetooth::connection_signature();
                            if sig != a.bt_sig {
                                a.bt_sig = sig;
                                SetTimer(Some(hwnd), TIMER_DEVCHANGE, 1500, None);
                            }
                            trim_memory();
                        }
                    }
                    _ => a.tick(),
                });
                // Every tick touches data pages of user32 / GDI / UI Automation, which count as the
                // process's own memory: hand them back right away, so Task Manager shows ~0.2 MB
                // nearly all the time instead of ~0.75 MB between the slower trims.
                trim_memory();
                LRESULT(0)
            }
            // A device was plugged in / removed (USB receiver, cable, Bluetooth link) or the PC woke
            // up: read again once things settle, if the user left that option on.
            // A device was plugged in or removed (HID interface arrival / removal, or any device
            // node change): read again once things settle, if the user left that option on.
            WM_DEVICECHANGE_MSG if matches!(wp.0, DBT_DEVNODES_CHANGED | DBT_DEVICEARRIVAL | DBT_DEVICEREMOVECOMPLETE) => {
                if refresh_on_change() {
                    SetTimer(Some(hwnd), TIMER_DEVCHANGE, 1500, None);
                }
                LRESULT(1)
            }
            WM_QUICK_DONE => {
                let devices = ui::take_result(lp);
                let ids = QUICK_IDS.with(|q| std::mem::take(&mut *q.borrow_mut()));
                with_app(|a| a.on_quick_result(devices, &ids));
                trim_memory();
                LRESULT(0)
            }
            WM_FOREGROUND => {
                with_app(|a| {
                    if a.strip_popup {
                        a.place();
                    }
                    if !a.mirrors.is_empty() {
                        a.sync_mirrors();
                    }
                });
                LRESULT(0)
            }
            WM_TRAY_PROBED => {
                with_app(|a| {
                    if a.align_left {
                        a.place();
                    }
                    a.sync_mirrors();
                });
                trim_memory();
                LRESULT(0)
            }
            WM_SHOW_UPDATED => {
                // Shown outside the timer handler, so the app is not borrowed while the box is open.
                let text = *Box::from_raw(lp.0 as *mut String);
                message(hwnd, &text, MB_OK | MB_ICONINFORMATION);
                LRESULT(0)
            }
            WM_UPDATE_CHECKED => {
                let check = *Box::from_raw(lp.0 as *mut batteryhub::update::Check);
                on_update_checked(hwnd, check);
                LRESULT(0)
            }
            WM_UPDATE_DOWNLOADED => {
                let result = *Box::from_raw(lp.0 as *mut Result<batteryhub::update::Verified, String>);
                on_update_downloaded(hwnd, result);
                LRESULT(0)
            }
            WM_TRAY if wp.0 as u32 == NOTIFY_UID => {
                // The low-battery notification closed or was clicked: its icon goes.
                const NIN_BALLOONHIDE: u32 = 0x403;
                const NIN_BALLOONTIMEOUT: u32 = 0x404;
                const NIN_BALLOONUSERCLICK: u32 = 0x405;
                if matches!((lp.0 & 0xFFFF) as u32, NIN_BALLOONHIDE | NIN_BALLOONTIMEOUT | NIN_BALLOONUSERCLICK) {
                    with_app(|a| a.end_notify());
                }
                LRESULT(0)
            }
            WM_TRAY => {
                if matches!((lp.0 & 0xFFFF) as u32, WM_RBUTTONUP | WM_CONTEXTMENU) {
                    show_menu(None);
                }
                LRESULT(0)
            }
            WM_MEASUREITEM if ui::measure_menu_item(lp) => LRESULT(1),
            WM_DRAWITEM if ui::draw_menu_item(lp) => LRESULT(1),
            WM_COPYDATA => {
                // From a dashboard: delete a device's measurements (it asked the user already).
                let cds = &*(lp.0 as *const windows::Win32::System::DataExchange::COPYDATASTRUCT);
                if cds.dwData == batteryhub::dashboard::COPY_RESET && !cds.lpData.is_null() {
                    let key = String::from_utf8_lossy(std::slice::from_raw_parts(cds.lpData as *const u8, cds.cbData as usize)).to_string();
                    with_app(|a| a.reset_history(&key));
                } else if cds.dwData == batteryhub::dashboard::COPY_DELETE && !cds.lpData.is_null() {
                    let key = String::from_utf8_lossy(std::slice::from_raw_parts(cds.lpData as *const u8, cds.cbData as usize)).to_string();
                    with_app(|a| a.delete_device(&key));
                } else if cds.dwData == batteryhub::dashboard::COPY_HELLO {
                    // A dashboard just opened: it gets every device right away (its device bar).
                    with_app(|a| a.send_to_dashboards());
                }
                LRESULT(1)
            }
            WM_HISTORY_SAVED => {
                with_app(|a| {
                    if wp.0 == 0 {
                        a.history.mark_dirty(); // try again at the next read
                    }
                });
                // An open dashboard reads the new file.
                batteryhub::dashboard::notify_history_changed();
                LRESULT(0)
            }
            // Sign-out, restart or shutdown: write the history before the process is ended.
            WM_ENDSESSION if wp.0 != 0 => {
                with_app(|a| a.save_history_now());
                LRESULT(0)
            }
            WM_POWERBROADCAST if wp.0 == PBT_APMSUSPEND => {
                with_app(|a| a.save_history_now());
                LRESULT(1)
            }
            WM_POWERBROADCAST if wp.0 == PBT_APMRESUMEAUTOMATIC => {
                if refresh_on_change() {
                    SetTimer(Some(hwnd), TIMER_DEVCHANGE, 5000, None);
                }
                LRESULT(1)
            }
            WM_TIMECHANGE => {
                batteryhub::dashboard::time_zone_changed();
                with_app(|a| a.card_cache.clear());
                LRESULT(0)
            }
            WM_SETTINGCHANGE | WM_DISPLAYCHANGE => {
                with_app(|a| {
                    a.refresh_settings(); // light/dark taskbar
                    a.paint(); // or DPI changed
                });
                LRESULT(0)
            }
            WM_DESTROY => {
                with_app(|a| {
                    a.save_history_now();
                    a.end_notify();
                    if !a.strip.0.is_null() {
                        let _ = DestroyWindow(a.strip);
                    }
                    a.remove_tray();
                });
                PostQuitMessage(0);
                LRESULT(0)
            }
            _ => {
                let (tc, nm, sh) = with_app(|a| (a.taskbar_created, a.names_msg, a.shell_msg)).unwrap_or((0, 0, 0));
                if sh != 0 && msg == sh {
                    // A window opened or closed: its task button comes or goes, so with the widget
                    // next to the taskbar icons, look again soon (the button animates in).
                    let code = (wp.0 & 0x7FFF) as u32;
                    if code == HSHELL_WINDOWCREATED || code == HSHELL_WINDOWDESTROYED {
                        with_app(|a| {
                            if !a.vertical && !a.fallback {
                                a.left_probes = LEFT_PROBES;
                                SetTimer(Some(hwnd), TIMER_LEFT_PROBE, 200, None);
                            }
                        });
                    }
                    return LRESULT(0);
                }
                if nm != 0 && msg == nm {
                    with_app(|a| a.reload_names());
                    return LRESULT(0);
                }
                if tc != 0 && msg == tc {
                    // Explorer restarted. The 1 s timer may already have put a new strip on the new
                    // taskbar, so the strip is not thrown away blindly (that left a second, orphaned
                    // strip behind): tick() keeps a live one and recreates a dead one. Fallback
                    // icons have to be added again.
                    with_app(|a| {
                        a.last_place = Default::default();
                        a.painted_for = Default::default();
                        a.tray.clear();
                        a.tick();
                        if a.fallback {
                            a.sync_tray();
                        }
                    });
                    return LRESULT(0);
                }
                DefWindowProcW(hwnd, msg, wp, lp)
            }
        }
    }
}

fn main() {
    unsafe {
        batteryhub::i18n::set_language(&language_choice());
        // `--report`: only the "Request support for a device" window (also while BatteryHub runs).
        if std::env::args().any(|a| a == "--report") {
            let _ = SetProcessDpiAwarenessContext(DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2);
            batteryhub::report_window::run_standalone();
            return;
        }
        // `--listen VID:PID`: diagnostic recording of a device's HID reports (see listen.rs).
        let args: Vec<String> = std::env::args().collect();
        // `--dashboard <tab> <device>` / `--rename <device>`: windows opened from the device menu,
        // each in its own short-lived process.
        if let Some(i) = args.iter().position(|a| a == "--dashboard") {
            let _ = SetProcessDpiAwarenessContext(DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2);
            batteryhub::dashboard::run_standalone(&args[i + 1..]);
            return;
        }
        if let Some(i) = args.iter().position(|a| a == "--rename") {
            let _ = SetProcessDpiAwarenessContext(DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2);
            batteryhub::rename::run_standalone(&args[i + 1..]);
            return;
        }
        if let Some(i) = args.iter().position(|a| a == "--listen") {
            batteryhub::listen::run(args.get(i + 1).map(|s| s.as_str()));
            return;
        }
        // One instance only (diagnostic runs with BH_DEBUG may start a second one for testing).
        // GetLastError must be read right after CreateMutexW: reading an environment variable that
        // is not set overwrites it (ERROR_ENVVAR_NOT_FOUND), which used to let every copy start.
        let _mutex = CreateMutexW(None, true, w!("Local\\BatteryHub.Taskbar"));
        let already_running = GetLastError() == ERROR_ALREADY_EXISTS;
        let second_ok = std::env::var_os("BH_DEBUG").is_some() || std::env::var_os("BH_SECOND_INSTANCE").is_some();
        if already_running && !second_ok {
            return;
        }
        let _ = SetProcessDpiAwarenessContext(DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2);
        // No text input anywhere: skip loading the IME / text services framework.
        let _ = windows::Win32::UI::Input::Ime::ImmDisableIME(u32::MAX);

        let hinst = GetModuleHandleW(None).unwrap_or_default();
        let arrow = LoadCursorW(None, IDC_ARROW).unwrap_or_default();
        for (class, proc_) in
            [(MAIN_CLASS, main_proc as unsafe extern "system" fn(HWND, u32, WPARAM, LPARAM) -> LRESULT), (STRIP_CLASS, strip_proc), (CARD_CLASS, card_proc)]
        {
            let wc = WNDCLASSEXW {
                cbSize: size_of::<WNDCLASSEXW>() as u32,
                lpfnWndProc: Some(proc_),
                hInstance: hinst.into(),
                hCursor: arrow,
                lpszClassName: class,
                ..Default::default()
            };
            RegisterClassExW(&wc);
        }
        let Ok(main) = CreateWindowExW(WS_EX_TOOLWINDOW, MAIN_CLASS, w!("BatteryHub Taskbar"), WS_POPUP, 0, 0, 0, 0, None, None, Some(hinst.into()), None)
        else {
            return;
        };
        let taskbar_created = RegisterWindowMessageW(w!("TaskbarCreated"));
        // Arrival / removal of any HID device (USB receivers, cables, Bluetooth HID links) is
        // reported to this window even though it is hidden.
        let mut filter = DEV_BROADCAST_DEVICEINTERFACE_W {
            dbcc_size: size_of::<DEV_BROADCAST_DEVICEINTERFACE_W>() as u32,
            dbcc_devicetype: DBT_DEVTYP_DEVICEINTERFACE.0,
            dbcc_classguid: windows::Win32::Devices::HumanInterfaceDevice::HidD_GetHidGuid(),
            ..Default::default()
        };
        let _ = RegisterDeviceNotificationW(HANDLE(main.0), &mut filter as *mut _ as *const c_void, DEVICE_NOTIFY_WINDOW_HANDLE);
        with_app(|a| {
            a.main = main;
            a.taskbar_created = taskbar_created;
            if RegisterShellHookWindow(main).as_bool() {
                a.shell_msg = RegisterWindowMessageW(w!("SHELLHOOK"));
            }
            a.refresh_settings();
            a.create_tooltip();
            a.history = batteryhub::history::History::load(EDITION, SETTINGS_KEY);
            a.names = settings::names(SETTINGS_KEY);
            a.hidden = settings::hidden(SETTINGS_KEY);
            a.saved_order = settings::order(SETTINGS_KEY);
            a.names_msg = batteryhub::rename::names_changed_message();
            // BH_FORCE_FALLBACK (diagnostics): start with notification-area icons. Otherwise the
            // fallback is decided by tick() after FALLBACK_AFTER_TICKS, so a taskbar that is not
            // ready yet at sign-in does not make icons flash up for a second.
            if std::env::var_os("BH_FORCE_FALLBACK").is_some() || a.icons_mode {
                a.set_fallback(true);
            } else if a.ensure_strip() {
                // Copies for other monitors right away (not at the first timer tick), so the
                // widget appears on all taskbars together as soon as their places are known.
                a.sync_mirrors();
            }
            a.bt_sig = batteryhub::drivers::bluetooth::connection_signature();
            a.start_poll();
        });
        SetTimer(Some(main), TIMER_POLL, refresh_minutes() * 60_000, None);
        SetTimer(Some(main), TIMER_PLACE, 1000, None);
        // Copies hide over full-screen windows at once, not only at the next placement tick.
        let _ = windows::Win32::UI::Accessibility::SetWinEventHook(
            EVENT_SYSTEM_FOREGROUND,
            EVENT_SYSTEM_FOREGROUND,
            None,
            Some(foreground_changed),
            0,
            0,
            WINEVENT_OUTOFCONTEXT,
        );
        SetTimer(Some(main), TIMER_BTWATCH, 3000, None);
        SetTimer(Some(main), TIMER_QUICK, QUICK_MS, None);
        if auto_update() {
            SetTimer(Some(main), TIMER_AUTO_UPDATE, AUTO_UPDATE_DELAY_MS, None);
        }
        // The Help menu's latest releases, loaded in the background now, so they are there the
        // first time the menu opens (not "Loading...").
        let _ = recent_releases();
        // Started by the setup after a new installation: say once that BatteryHub is free (people
        // were found selling it). Its own thread, so the strip keeps working while it is open.
        if batteryhub::util::reg_get_string(SETTINGS_KEY, "FreeNotice").is_some() {
            batteryhub::util::reg_delete_value(SETTINGS_KEY, "FreeNotice");
            std::thread::spawn(free_notice);
        }
        // Started by the setup after an update: say so once.
        if let Some(old) = batteryhub::util::reg_get_string(SETTINGS_KEY, "UpdatedFrom") {
            batteryhub::util::reg_delete_value(SETTINGS_KEY, "UpdatedFrom");
            if batteryhub::install::label_of(&old) != batteryhub::install::version_label() {
                with_app(|a| a.updated_from = Some(old));
                SetTimer(Some(main), TIMER_UPDATED, 2000, None);
            }
        }

        let mut msg = MSG::default();
        while GetMessageW(&mut msg, None, 0, 0).as_bool() {
            // Tab / Enter / Esc in the "Request support for a device" window.
            if batteryhub::report_window::pre_translate(&msg) {
                continue;
            }
            let _ = TranslateMessage(&msg);
            DispatchMessageW(&msg);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vertical_taskbar_column() {
        // Two devices (icon, level, bolt) and one (icon, level) in a 48 px wide column.
        let pieces = [(Some(0), 16, 16), (Some(0), 26, 14), (Some(0), 8, 11), (Some(1), 16, 16), (Some(1), 30, 14)];
        let (pos, h, hits) = column_layout(&pieces, 48, 8, 2, 12, 2);
        assert_eq!(pos[0], (16, 8, true)); // icon centred on its own line
        assert_eq!(pos[1].1, 8 + 16 + 2); // level on the next line
        assert!(pos[2].2 && pos[2].0 >= pos[1].0 + 26); // bolt beside the level (fits)
        assert!(pos.iter().all(|p| p.0 >= 0 && p.0 < 48));
        assert_eq!(hits.len(), 2);
        assert_eq!((hits[0].0, hits[1].1), (0, h)); // the rows cover the whole column
        assert_eq!(hits[0].1, hits[1].0); // and touch each other
        assert!(pos[3].1 > pos[1].1 + 14); // second device below the first
        // Too narrow for the bolt: it is left out instead of overflowing.
        let (pos, _, _) = column_layout(&pieces[..3], 32, 8, 2, 12, 2);
        assert!(!pos[2].2);
        // The "no devices" glyph alone.
        let (pos, h, hits) = column_layout(&[(None, 16, 16)], 40, 8, 2, 12, 2);
        assert_eq!((pos[0], h, hits.len()), ((12, 8, true), 32, 0));
    }

    #[test]
    fn widgets_push_the_strip_left() {
        // Free spot: unchanged.
        assert_eq!(shift_left_of(1500, 100, 4, &[(1300, 1400)]), 1500);
        // Overlaps a meter at 1550..1650: moves left of it.
        assert_eq!(shift_left_of(1560, 100, 4, &[(1550, 1650)]), 1446);
        // Two widgets side by side: ends left of both.
        assert_eq!(shift_left_of(1560, 100, 4, &[(1550, 1650), (1400, 1500)]), 1296);
    }

    #[test]
    fn earbuds_icon_greys_the_bud_that_is_not_reported() {
        let both = buds_mask(32, true, true);
        let right_only = buds_mask(32, false, true);
        let sum = |m: &Mask, left: bool| -> u32 {
            (0..m.h).flat_map(|y| (0..m.w).map(move |x| (x, y))).filter(|(x, _)| (x * 2 < m.w) == left).map(|(x, y)| m.a[(y * m.w + x) as usize] as u32).sum()
        };
        assert!(sum(&both, true) > 1000 && sum(&both, false) > 1000);
        assert_eq!(sum(&right_only, false), sum(&both, false));
        assert!(sum(&right_only, true) * 2 < sum(&both, true));
        if let Some(path) = std::env::var_os("BH_DUMP_BUDS") {
            // Big preview for a look: both buds over the right one alone.
            let m = buds_mask(96, true, true);
            let r = buds_mask(96, false, true);
            let mut out = format!(
                "P2
{} {}
255
",
                m.w,
                m.h * 2
            );
            for a in m.a.iter().chain(r.a.iter()) {
                out.push_str(&format!("{} ", 255 - a));
            }
            std::fs::write(path, out).unwrap();
        }
    }
}
