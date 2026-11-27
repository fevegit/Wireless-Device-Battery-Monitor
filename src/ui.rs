//! Win32 / GDI helpers (fonts, colours, background polling, autostart).
use std::ffi::c_void;

use windows::Win32::Foundation::{COLORREF, HWND, LPARAM, RECT, SIZE, WPARAM};
use windows::Win32::Graphics::Gdi::{
    ANTIALIASED_QUALITY, BI_RGB, BITMAPINFO, BITMAPINFOHEADER, CLIP_DEFAULT_PRECIS, CreateBitmap, CreateCompatibleDC, CreateDIBSection, CreateFontW,
    DEFAULT_CHARSET, DIB_RGB_COLORS, DT_CENTER, DT_NOPREFIX, DT_SINGLELINE, DT_VCENTER, DeleteDC, DeleteObject, DrawTextW, GetTextExtentPoint32W, HDC, HFONT,
    HGDIOBJ, OUT_DEFAULT_PRECIS, SelectObject, SetBkMode, SetTextColor, TRANSPARENT,
};
use windows::Win32::System::Registry::{HKEY_CURRENT_USER, RRF_RT_REG_DWORD, RegGetValueW};
use windows::Win32::UI::WindowsAndMessaging::{CreateIconIndirect, HICON, ICONINFO, PostMessageW};
use windows::core::{HSTRING, PCWSTR};

use crate::device::DeviceStatus;
use crate::util;

/// Windows "apps / taskbar use light theme" setting.
pub fn light_theme(value: &str) -> bool {
    let mut v: u32 = 0;
    let mut size = 4u32;
    let r = unsafe {
        RegGetValueW(
            HKEY_CURRENT_USER,
            &HSTRING::from("Software\\Microsoft\\Windows\\CurrentVersion\\Themes\\Personalize"),
            &HSTRING::from(value),
            RRF_RT_REG_DWORD,
            None,
            Some(&mut v as *mut u32 as *mut c_void),
            Some(&mut size),
        )
    };
    r.is_ok() && v != 0
}

pub fn taskbar_is_light() -> bool {
    light_theme("SystemUsesLightTheme")
}

pub fn apps_are_light() -> bool {
    light_theme("AppsUseLightTheme")
}

pub const fn rgb(r: u8, g: u8, b: u8) -> COLORREF {
    COLORREF(r as u32 | (g as u32) << 8 | (b as u32) << 16)
}

pub fn split(c: COLORREF) -> (u8, u8, u8) {
    (c.0 as u8, (c.0 >> 8) as u8, (c.0 >> 16) as u8)
}

/// Green lightning bolt: the device is charging.
pub fn charging_color(light: bool) -> COLORREF {
    if light { rgb(16, 124, 16) } else { rgb(108, 203, 95) }
}

/// Blue lightning bolt: charged to 100% while still on power.
pub fn full_color(light: bool) -> COLORREF {
    if light { rgb(0, 120, 212) } else { rgb(96, 205, 255) }
}

/// Red: at or below the device's warning level.
pub fn low_color(light: bool) -> COLORREF {
    if light { rgb(196, 30, 40) } else { rgb(255, 90, 90) }
}

/// Bolt colour for a device on power, None when it runs on battery.
pub fn bolt_color(s: &DeviceStatus, light: bool) -> Option<COLORREF> {
    if s.is_full() {
        Some(full_color(light))
    } else if s.is_charging() {
        Some(charging_color(light))
    } else {
        None
    }
}

/// Colour of a battery level: red when low (per-device `threshold`), green while charging, blue
/// when full, grey when asleep, otherwise `normal`.
pub fn level_color(s: &DeviceStatus, light: bool, normal: COLORREF, threshold: i32) -> COLORREF {
    if s.asleep || !s.connected {
        return if light { rgb(140, 140, 140) } else { rgb(130, 130, 130) };
    }
    if let Some(c) = bolt_color(s, light) {
        return c;
    }
    if crate::settings::is_low(s, threshold) {
        return low_color(light);
    }
    normal
}

pub fn font(height: i32, weight: i32, face: &str) -> HFONT {
    unsafe {
        CreateFontW(-height, 0, 0, 0, weight, 0, 0, 0, DEFAULT_CHARSET, OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS, ANTIALIASED_QUALITY, 0, &HSTRING::from(face))
    }
}

pub fn text_width(dc: HDC, text: &str) -> i32 {
    let w: Vec<u16> = text.encode_utf16().collect();
    let mut sz = SIZE::default();
    unsafe {
        let _ = GetTextExtentPoint32W(dc, &w, &mut sz);
    }
    sz.cx
}

/// Draws `text` with DrawTextW into `rc`.
pub fn draw_text(dc: HDC, text: &str, rc: &mut RECT, flags: windows::Win32::Graphics::Gdi::DRAW_TEXT_FORMAT) {
    let mut w: Vec<u16> = text.encode_utf16().collect();
    unsafe {
        DrawTextW(dc, &mut w, rc, flags | DT_NOPREFIX);
    }
}

/// Renders a square tray icon: the level number (or `?`) in `color`, with a thin level bar below.
/// GDI text has no alpha, so it is drawn white-on-black and the luminance becomes the alpha.
pub fn number_icon(text: &str, color: COLORREF, level: i32, size: i32, light: bool) -> Option<HICON> {
    tray_number_icon(text, color, level, size, light, None)
}

/// Experimental native tray layout: a device glyph above its battery number.
/// Windows owns the icon slot; the existing numeric layout remains the fallback.
pub fn device_number_icon(text: &str, color: COLORREF, level: i32, size: i32, light: bool, glyph: char) -> Option<HICON> {
    if size < 16 {
        return number_icon(text, color, level, size, light);
    }
    tray_number_icon(text, color, level, size, light, Some(glyph))
        .or_else(|| number_icon(text, color, level, size, light))
}

fn tray_number_icon(text: &str, color: COLORREF, level: i32, size: i32, light: bool, glyph: Option<char>) -> Option<HICON> {
    if size <= 0 {
        return None;
    }
    unsafe {
        let dc = CreateCompatibleDC(None);
        let bmi = BITMAPINFO {
            bmiHeader: BITMAPINFOHEADER {
                biSize: size_of::<BITMAPINFOHEADER>() as u32,
                biWidth: size,
                biHeight: -size, // top-down
                biPlanes: 1,
                biBitCount: 32,
                biCompression: BI_RGB.0,
                ..Default::default()
            },
            ..Default::default()
        };
        let mut bits: *mut c_void = std::ptr::null_mut();
        let Ok(bmp) = CreateDIBSection(Some(dc), &bmi, DIB_RGB_COLORS, &mut bits, None, 0) else {
            let _ = DeleteDC(dc);
            return None;
        };
        let old = SelectObject(dc, HGDIOBJ(bmp.0));
        let px = std::slice::from_raw_parts_mut(bits as *mut u32, (size * size) as usize);
        px.fill(0);

        // A native tray slot is square. In glyph mode use its top half for the
        // device and the rest for digits, with no separate level bar.
        let bar_h = if glyph.is_some() { 0 } else { (size / 8).max(2) };
        let text_top = if glyph.is_some() { size / 2 } else { -1 };
        let text_h = if glyph.is_some() { size } else { size - bar_h - 1 };
        SetBkMode(dc, TRANSPARENT);
        SetTextColor(dc, rgb(255, 255, 255));
        if let Some(g) = glyph {
            let gf = font((text_top - 1).max(6), 400, icon_font_face());
            let before = SelectObject(dc, HGDIOBJ(gf.0));
            let mut rect = RECT { left: 0, top: 0, right: size, bottom: text_top };
            draw_text(dc, &g.to_string(), &mut rect, DT_CENTER | DT_VCENTER | DT_SINGLELINE);
            SelectObject(dc, before);
            let _ = DeleteObject(HGDIOBJ(gf.0));
        }
        let mut height = if glyph.is_some() { text_h - text_top } else { text_h + size / 6 };
        let mut f = font(height, 700, "Segoe UI");
        let mut prev = SelectObject(dc, HGDIOBJ(f.0));
        while height > 6 && text_width(dc, text) > size {
            SelectObject(dc, prev);
            let _ = DeleteObject(HGDIOBJ(f.0));
            height -= 1;
            f = font(height, 700, "Segoe UI");
            prev = SelectObject(dc, HGDIOBJ(f.0));
        }
        SetBkMode(dc, TRANSPARENT);
        SetTextColor(dc, rgb(255, 255, 255));
        let mut rc = RECT { left: -2, top: text_top, right: size + 2, bottom: text_h };
        draw_text(dc, text, &mut rc, DT_CENTER | DT_VCENTER | DT_SINGLELINE);
        SelectObject(dc, prev);
        let _ = DeleteObject(HGDIOBJ(f.0));

        let (r, g, b) = split(color);
        for p in px.iter_mut() {
            let a = (*p & 0xFF).max((*p >> 8) & 0xFF).max((*p >> 16) & 0xFF);
            *p = premul(r, g, b, a as u8);
        }
        // Level bar: faint track plus a filled part (numeric layout only).
        if glyph.is_none() && level >= 0 {
            let track = if light { (0u8, 0u8, 0u8, 70u8) } else { (255, 255, 255, 70) };
            let fill_w = ((size - 2) * level.clamp(0, 100) + 50) / 100;
            for y in size - bar_h..size {
                for x in 1..size - 1 {
                    px[(y * size + x) as usize] = if x - 1 < fill_w.max(1) { premul(r, g, b, 255) } else { premul(track.0, track.1, track.2, track.3) };
                }
            }
        }
        SelectObject(dc, old);
        let _ = DeleteDC(dc);

        let mask = CreateBitmap(size, size, 1, 1, None);
        let info = ICONINFO { fIcon: true.into(), hbmColor: bmp, hbmMask: mask, ..Default::default() };
        let icon = CreateIconIndirect(&info).ok();
        let _ = DeleteObject(HGDIOBJ(bmp.0));
        let _ = DeleteObject(HGDIOBJ(mask.0));
        icon
    }
}

fn premul(r: u8, g: u8, b: u8, a: u8) -> u32 {
    let m = |c: u8| (c as u32 * a as u32 / 255) & 0xFF;
    (a as u32) << 24 | m(r) << 16 | m(g) << 8 | m(b)
}

// ---- dark / light menus and tooltips --------------------------------------------------------

type SetPreferredAppMode = unsafe extern "system" fn(i32) -> i32;
type FlushMenuThemes = unsafe extern "system" fn();
type AllowDarkModeForWindow = unsafe extern "system" fn(HWND, i32) -> i32;

struct UxTheme {
    set_mode: Option<SetPreferredAppMode>,
    flush: Option<FlushMenuThemes>,
    allow_window: Option<AllowDarkModeForWindow>,
}

/// uxtheme.dll's unnamed exports (ordinals 133, 135, 136) that Explorer itself uses for dark
/// context menus (Windows 10 1903 and later). Missing ones are simply skipped.
fn uxtheme() -> &'static UxTheme {
    static UX: std::sync::OnceLock<UxTheme> = std::sync::OnceLock::new();
    UX.get_or_init(|| unsafe {
        use windows::Win32::System::LibraryLoader::{GetProcAddress, LOAD_LIBRARY_SEARCH_SYSTEM32, LoadLibraryExW};
        let Ok(m) = LoadLibraryExW(windows::core::w!("uxtheme.dll"), None, LOAD_LIBRARY_SEARCH_SYSTEM32) else {
            return UxTheme { set_mode: None, flush: None, allow_window: None };
        };
        let ord = |n: usize| GetProcAddress(m, windows::core::PCSTR(n as *const u8));
        UxTheme {
            allow_window: ord(133).map(|f| std::mem::transmute::<_, AllowDarkModeForWindow>(f)),
            set_mode: ord(135).map(|f| std::mem::transmute::<_, SetPreferredAppMode>(f)),
            flush: ord(136).map(|f| std::mem::transmute::<_, FlushMenuThemes>(f)),
        }
    })
}

/// Makes the process's popup menus dark or light (to match the taskbar they open from).
pub fn set_menu_theme(owner: HWND, dark: bool) {
    let ux = uxtheme();
    unsafe {
        if let Some(f) = ux.allow_window {
            f(owner, dark as i32);
        }
        if let Some(f) = ux.set_mode {
            f(if dark { 2 } else { 3 }); // ForceDark / ForceLight
        }
        if let Some(f) = ux.flush {
            f();
        }
    }
}

/// Dark or light tooltip (the "DarkMode_Explorer" theme class Explorer uses).
pub fn set_tooltip_theme(tip: HWND, dark: bool) {
    unsafe {
        let theme = if dark { windows::core::w!("DarkMode_Explorer") } else { windows::core::w!("Explorer") };
        let _ = windows::Win32::UI::Controls::SetWindowTheme(tip, theme, PCWSTR::null());
    }
}

// ---- background polling ------------------------------------------------------------------------

/// Runs `poll_devices(rescan)` on a worker thread and posts the result to `hwnd` as `msg`
/// (LPARAM = Box<Vec<DeviceStatus>> raw pointer; the receiver must take it back with `take_result`).
pub fn poll_async(hwnd: HWND, msg: u32, rescan: bool) {
    run_async(hwnd, msg, move || crate::device::poll_devices(rescan));
}

/// Runs `read` on a worker thread and posts its result to `hwnd` as `msg` (see `take_result`).
pub fn run_async(hwnd: HWND, msg: u32, read: impl FnOnce() -> Vec<DeviceStatus> + Send + 'static) {
    let h = hwnd.0 as usize;
    std::thread::spawn(move || {
        let devices = read();
        let ptr = Box::into_raw(Box::new(devices));
        unsafe {
            if PostMessageW(Some(HWND(h as *mut c_void)), msg, WPARAM(0), LPARAM(ptr as isize)).is_err() {
                drop(Box::from_raw(ptr));
            }
        }
    });
}

/// # Safety
/// `lparam` must come from a message posted by `poll_async`.
pub unsafe fn take_result(lparam: LPARAM) -> Vec<DeviceStatus> {
    unsafe { *Box::from_raw(lparam.0 as *mut Vec<DeviceStatus>) }
}

// ---- autostart ---------------------------------------------------------------------------------

const RUN_KEY: &str = "Software\\Microsoft\\Windows\\CurrentVersion\\Run";

pub fn exe_path() -> String {
    let mut buf = [0u16; 1024];
    let n = unsafe { windows::Win32::System::LibraryLoader::GetModuleFileNameW(None, &mut buf) } as usize;
    String::from_utf16_lossy(&buf[..n])
}

pub fn autostart_enabled(name: &str) -> bool {
    util::reg_get_string(RUN_KEY, name).is_some_and(|v| v.to_lowercase().contains(&exe_path().to_lowercase()))
}

pub fn set_autostart(name: &str, on: bool) {
    if on {
        util::reg_set_string(RUN_KEY, name, &format!("\"{}\"", exe_path()));
    } else {
        util::reg_delete_value(RUN_KEY, name);
    }
}

pub fn wstr(s: &str) -> HSTRING {
    HSTRING::from(s)
}

pub fn pcw(h: &HSTRING) -> PCWSTR {
    PCWSTR(h.as_ptr())
}

/// Copies `s` into a fixed UTF-16 buffer (truncating), as NOTIFYICONDATAW wants.
pub fn fill_wide<const N: usize>(dst: &mut [u16; N], s: &str) {
    dst.fill(0);
    for (i, c) in s.encode_utf16().take(N - 1).enumerate() {
        dst[i] = c;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dev(percent: i32, charging: bool, full: bool) -> DeviceStatus {
        DeviceStatus { percent, charging, full, ..Default::default() }
    }

    #[test]
    fn bolt_is_green_while_charging_and_blue_when_full() {
        for light in [false, true] {
            assert_eq!(bolt_color(&dev(40, true, false), light), Some(charging_color(light)));
            assert_eq!(bolt_color(&dev(99, true, false), light), Some(charging_color(light)));
            assert_eq!(bolt_color(&dev(100, true, false), light), Some(full_color(light)));
            assert_eq!(bolt_color(&dev(100, true, true), light), Some(full_color(light)));
            assert_eq!(bolt_color(&dev(-1, false, true), light), Some(full_color(light)));
            assert_eq!(bolt_color(&dev(80, false, false), light), None);
        }
    }

    #[test]
    fn red_only_at_or_below_the_chosen_level_and_never_while_charging() {
        let normal = rgb(1, 2, 3);
        assert_eq!(level_color(&dev(30, false, false), false, normal, 30), low_color(false));
        assert_eq!(level_color(&dev(31, false, false), false, normal, 30), normal);
        assert_eq!(level_color(&dev(10, true, false), false, normal, 30), charging_color(false));
        assert_eq!(level_color(&dev(50, false, false), false, normal, 50), low_color(false));
    }
}

// ---- menu icons --------------------------------------------------------------------------------

/// Segoe Fluent Icons code points used in the menus (one icon set, the one Windows 11 uses).
pub mod glyph {
    /// Not a font glyph: stands for the drawn earbuds icon (crate::gui::earbuds_icon).
    pub const EARBUDS: char = '\u{F0000}';
    pub const DASHBOARD: char = '\u{F246}';
    /// Segoe MDL2 Assets (Windows 10) has no dashboard glyph: four tiles instead.
    pub const DASHBOARD_MDL2: char = '\u{E80A}';
    pub const HISTORY: char = '\u{E81C}';
    pub const STATISTICS: char = '\u{E9D2}';
    pub const RENAME: char = '\u{E8AC}';
    pub const RESET: char = '\u{E7A7}';
    pub const WARNING: char = '\u{E7BA}';
    pub const BELL: char = '\u{EA8F}';
    pub const REFRESH: char = '\u{E72C}';
    pub const SYNC: char = '\u{E895}';
    pub const SETTINGS: char = '\u{E713}';
    pub const MONITOR: char = '\u{E7F4}';
    pub const POWER: char = '\u{E7E8}';
    pub const DOWNLOAD: char = '\u{E896}';
    pub const MAIL: char = '\u{E715}';
    pub const EXIT: char = '\u{E8BB}';
    pub const INFO: char = '\u{E946}';
    pub const LANGUAGE: char = '\u{E774}';
    pub const VIEW: char = '\u{E890}';
    pub const LEFT: char = '\u{E76B}';
    pub const RIGHT: char = '\u{E76C}';
    pub const UP: char = '\u{E70E}';
    pub const DOWN: char = '\u{E70D}';
    pub const DELETE: char = '\u{E74D}';
    pub const CHECK: char = '\u{E73E}';
    pub const COLOR: char = '\u{E790}';
}

/// Whether Segoe Fluent Icons is installed (Windows 11); otherwise Segoe MDL2 Assets is used.
pub fn has_fluent_icons() -> bool {
    static HAS: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *HAS.get_or_init(|| unsafe {
        use windows::Win32::Graphics::Gdi::GetTextFaceW;
        let f = font(16, 400, "Segoe Fluent Icons");
        let dc = CreateCompatibleDC(None);
        let old = SelectObject(dc, HGDIOBJ(f.0));
        let mut face = [0u16; 64];
        GetTextFaceW(dc, Some(&mut face));
        SelectObject(dc, old);
        let _ = DeleteDC(dc);
        let _ = DeleteObject(HGDIOBJ(f.0));
        util::from_wide(&face).eq_ignore_ascii_case("Segoe Fluent Icons")
    })
}

pub fn icon_font_face() -> &'static str {
    if has_fluent_icons() { "Segoe Fluent Icons" } else { "Segoe MDL2 Assets" }
}

/// A glyph as a 32-bit premultiplied bitmap of `size` px for a menu item (white on dark menus,
/// black on light ones). The caller deletes it after the menu closed.
pub fn glyph_bitmap(g: char, size: i32, dark: bool) -> Option<windows::Win32::Graphics::Gdi::HBITMAP> {
    let g = if g == glyph::DASHBOARD && !has_fluent_icons() { glyph::DASHBOARD_MDL2 } else { g };
    unsafe {
        let dc = CreateCompatibleDC(None);
        let bmi = BITMAPINFO {
            bmiHeader: BITMAPINFOHEADER {
                biSize: size_of::<BITMAPINFOHEADER>() as u32,
                biWidth: size,
                biHeight: -size,
                biPlanes: 1,
                biBitCount: 32,
                biCompression: BI_RGB.0,
                ..Default::default()
            },
            ..Default::default()
        };
        let mut bits: *mut c_void = std::ptr::null_mut();
        let bmp = CreateDIBSection(Some(dc), &bmi, DIB_RGB_COLORS, &mut bits, None, 0).ok()?;
        let f = font(size, 400, icon_font_face());
        let old_b = SelectObject(dc, HGDIOBJ(bmp.0));
        let old_f = SelectObject(dc, HGDIOBJ(f.0));
        let px = std::slice::from_raw_parts_mut(bits as *mut u32, (size * size) as usize);
        px.fill(0);
        if g == glyph::EARBUDS {
            let (r, gg, b) = if dark { (255, 255, 255) } else { (0, 0, 0) };
            let a = crate::gui::earbuds_icon(size, true, true);
            for (p, a) in px.iter_mut().zip(a) {
                *p = premul(r, gg, b, a);
            }
            SelectObject(dc, old_f);
            SelectObject(dc, old_b);
            let _ = DeleteObject(HGDIOBJ(f.0));
            let _ = DeleteDC(dc);
            return Some(bmp);
        }
        SetBkMode(dc, TRANSPARENT);
        SetTextColor(dc, rgb(255, 255, 255));
        let mut rc = RECT { left: 0, top: 0, right: size, bottom: size };
        draw_text(dc, &g.to_string(), &mut rc, DT_CENTER | DT_VCENTER | DT_SINGLELINE);
        let _ = windows::Win32::Graphics::Gdi::GdiFlush();
        let (r, gg, b) = if dark { (255, 255, 255) } else { (0, 0, 0) };
        for p in px.iter_mut() {
            let a = (((*p & 0xFF) + ((*p >> 8) & 0xFF) + ((*p >> 16) & 0xFF)) / 3) as u8;
            *p = premul(r, gg, b, a);
        }
        SelectObject(dc, old_f);
        SelectObject(dc, old_b);
        let _ = DeleteObject(HGDIOBJ(f.0));
        let _ = DeleteDC(dc);
        Some(bmp)
    }
}

/// Icons of one popup menu and its submenus: set while building, deleted on drop (after
/// TrackPopupMenu returned).
pub struct MenuIcons {
    size: i32,
    dark: bool,
    bitmaps: Vec<windows::Win32::Graphics::Gdi::HBITMAP>,
    /// (menu, item, by position, glyph): the icons again, for ModernMenu.
    glyphs: Vec<(usize, u32, bool, char)>,
}

impl MenuIcons {
    pub fn new(owner: HWND, dark: bool) -> Self {
        use windows::Win32::UI::HiDpi::{GetDpiForWindow, GetSystemMetricsForDpi};
        use windows::Win32::UI::WindowsAndMessaging::SM_CXSMICON;
        let dpi = unsafe { GetDpiForWindow(owner) }.max(96);
        let size = unsafe { GetSystemMetricsForDpi(SM_CXSMICON, dpi) }.max(16);
        MenuIcons { size, dark, bitmaps: Vec::new(), glyphs: Vec::new() }
    }

    /// Gives menu item `item` (a command id, or a position when `by_pos`) the icon `g`.
    pub fn set(&mut self, menu: windows::Win32::UI::WindowsAndMessaging::HMENU, item: u32, by_pos: bool, g: char) {
        self.glyphs.push((menu.0 as usize, item, by_pos, g));
        use windows::Win32::UI::WindowsAndMessaging::{MENUITEMINFOW, MIIM_BITMAP, SetMenuItemInfoW};
        let Some(bmp) = glyph_bitmap(g, self.size, self.dark) else { return };
        let mii = MENUITEMINFOW { cbSize: size_of::<MENUITEMINFOW>() as u32, fMask: MIIM_BITMAP, hbmpItem: bmp, ..Default::default() };
        unsafe {
            let _ = SetMenuItemInfoW(menu, item, by_pos, &mii);
        }
        self.bitmaps.push(bmp);
    }

    /// The icon given to the item at `pos` (command id `id`) of `menu`.
    fn glyph_of(&self, menu: windows::Win32::UI::WindowsAndMessaging::HMENU, pos: u32, id: u32) -> Option<char> {
        let m = menu.0 as usize;
        self.glyphs.iter().rev().find(|(mm, item, by_pos, _)| *mm == m && if *by_pos { *item == pos } else { *item == id && id != 0 }).map(|g| g.3)
    }

    /// A checked item shows its check mark instead of its icon (no overlap in the gutter).
    pub fn check_or_icon(menu: windows::Win32::UI::WindowsAndMessaging::HMENU) {
        use windows::Win32::UI::WindowsAndMessaging::{MENUINFO, MIM_STYLE, MNS_CHECKORBMP, SetMenuInfo};
        let mi = MENUINFO { cbSize: size_of::<MENUINFO>() as u32, fMask: MIM_STYLE, dwStyle: MNS_CHECKORBMP, ..Default::default() };
        unsafe {
            let _ = SetMenuInfo(menu, &mi);
        }
    }
}

impl Drop for MenuIcons {
    fn drop(&mut self) {
        for b in self.bitmaps.drain(..) {
            unsafe {
                let _ = DeleteObject(HGDIOBJ(b.0));
            }
        }
    }
}

// ---- Windows 11 style menus --------------------------------------------------------------------

/// What an owner-drawn menu item shows.
struct MenuItemData {
    text: String,
    glyph: Option<char>,
    popup: bool,
    separator: bool,
}

/// Colours, sizes and fonts of the open menu (one menu is open at a time).
struct MenuStyle {
    s: f32,
    font: HFONT,
    icons: HFONT,
    chevron: HFONT,
    bg: COLORREF,
    hover: COLORREF,
    text: COLORREF,
    disabled: COLORREF,
    line: COLORREF,
}

thread_local! {
    static MENU_STYLE: std::cell::RefCell<Option<MenuStyle>> = const { std::cell::RefCell::new(None) };
}

/// A popup menu (and its submenus) drawn like Windows 11's own context menus: taller rows,
/// Fluent icons, a rounded highlight, check marks in the icon column and a chevron for
/// submenus. Built over a normal menu, so keyboard use and submenus stay Windows' own. Keep it
/// until TrackPopupMenu returned; it frees its fonts and brush on drop.
pub struct ModernMenu {
    /// Rounds the corners of the menu windows (#32768) while this menu is open.
    hook: Option<windows::Win32::UI::WindowsAndMessaging::HHOOK>,
    /// Boxed: the menu items point at them, so they must not move when the list grows.
    #[allow(clippy::vec_box)]
    items: Vec<Box<MenuItemData>>,
    brush: windows::Win32::Graphics::Gdi::HBRUSH,
}

impl ModernMenu {
    pub fn apply(menu: windows::Win32::UI::WindowsAndMessaging::HMENU, icons: &MenuIcons, owner: HWND, dark: bool) -> Self {
        use windows::Win32::Graphics::Gdi::{CLEARTYPE_QUALITY, CreateSolidBrush};
        use windows::Win32::UI::HiDpi::GetDpiForWindow;
        use windows::Win32::UI::WindowsAndMessaging::{MENUINFO, MIM_APPLYTOSUBMENUS, MIM_BACKGROUND, SetMenuInfo};
        let s = unsafe { GetDpiForWindow(owner) }.max(96) as f32 / 96.0;
        let px = |v: f32| (v * s).round() as i32;
        let face = crate::gui::text_face(false);
        let text_font = unsafe {
            CreateFontW(-px(12.0), 0, 0, 0, 400, 0, 0, 0, DEFAULT_CHARSET, OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS, CLEARTYPE_QUALITY, 0, &HSTRING::from(face))
        };
        let (bg, hover, text, disabled, line) = if dark {
            (rgb(44, 44, 44), rgb(61, 61, 61), rgb(255, 255, 255), rgb(120, 120, 120), rgb(64, 64, 64))
        } else {
            (rgb(249, 249, 249), rgb(234, 234, 234), rgb(26, 26, 26), rgb(160, 160, 160), rgb(226, 226, 226))
        };
        let style = MenuStyle {
            s,
            font: text_font,
            icons: font(px(14.0), 400, icon_font_face()),
            chevron: font(px(8.0), 400, icon_font_face()),
            bg,
            hover,
            text,
            disabled,
            line,
        };
        MENU_STYLE.with(|m| {
            if let Some(old) = m.borrow_mut().replace(style) {
                free_style(old);
            }
        });
        let brush = unsafe { CreateSolidBrush(bg) };
        let mi = MENUINFO { cbSize: size_of::<MENUINFO>() as u32, fMask: MIM_BACKGROUND | MIM_APPLYTOSUBMENUS, hbrBack: brush, ..Default::default() };
        unsafe {
            let _ = SetMenuInfo(menu, &mi);
        }
        let hook = unsafe {
            windows::Win32::UI::WindowsAndMessaging::SetWindowsHookExW(
                windows::Win32::UI::WindowsAndMessaging::WH_CALLWNDPROC,
                Some(round_menu_windows),
                None,
                windows::Win32::System::Threading::GetCurrentThreadId(),
            )
            .ok()
        };
        let mut me = ModernMenu { hook, items: Vec::new(), brush };
        me.convert(menu, icons);
        me
    }

    fn convert(&mut self, menu: windows::Win32::UI::WindowsAndMessaging::HMENU, icons: &MenuIcons) {
        use windows::Win32::UI::WindowsAndMessaging::*;
        let n = unsafe { GetMenuItemCount(Some(menu)) };
        for pos in 0..n.max(0) as u32 {
            let mut buf = [0u16; 512];
            let mut mii = MENUITEMINFOW {
                cbSize: size_of::<MENUITEMINFOW>() as u32,
                fMask: MIIM_FTYPE | MIIM_ID | MIIM_SUBMENU | MIIM_STRING,
                dwTypeData: windows::core::PWSTR(buf.as_mut_ptr()),
                cch: buf.len() as u32 - 1,
                ..Default::default()
            };
            if unsafe { GetMenuItemInfoW(menu, pos, true, &mut mii) }.is_err() {
                continue;
            }
            let separator = mii.fType.0 & MFT_SEPARATOR.0 != 0;
            let popup = !mii.hSubMenu.0.is_null();
            let text = util::from_wide(&buf[..(mii.cch as usize).min(buf.len())]);
            let glyph = icons.glyph_of(menu, pos, mii.wID);
            let data = Box::new(MenuItemData { text, glyph, popup, separator });
            let set = MENUITEMINFOW {
                cbSize: size_of::<MENUITEMINFOW>() as u32,
                fMask: MIIM_FTYPE | MIIM_DATA | MIIM_BITMAP,
                fType: MENU_ITEM_TYPE(mii.fType.0 | MFT_OWNERDRAW.0),
                dwItemData: &*data as *const MenuItemData as usize,
                hbmpItem: windows::Win32::Graphics::Gdi::HBITMAP::default(),
                ..Default::default()
            };
            unsafe {
                let _ = SetMenuItemInfoW(menu, pos, true, &set);
            }
            self.items.push(data);
            if popup {
                self.convert(mii.hSubMenu, icons);
            }
        }
    }
}

/// WH_CALLWNDPROC hook: a menu window being created gets Windows 11's rounded corners.
unsafe extern "system" fn round_menu_windows(code: i32, wp: WPARAM, lp: LPARAM) -> windows::Win32::Foundation::LRESULT {
    use windows::Win32::UI::WindowsAndMessaging::{CWPSTRUCT, CallNextHookEx, GetClassNameW, HHOOK, WM_CREATE};
    unsafe {
        if code >= 0 {
            let m = &*(lp.0 as *const CWPSTRUCT);
            if m.message == WM_CREATE {
                let mut class = [0u16; 16];
                let n = GetClassNameW(m.hwnd, &mut class) as usize;
                if &class[..n] == "#32768".encode_utf16().collect::<Vec<u16>>().as_slice() {
                    let round: i32 = 2; // DWMWCP_ROUND
                    let _ = windows::Win32::Graphics::Dwm::DwmSetWindowAttribute(
                        m.hwnd,
                        windows::Win32::Graphics::Dwm::DWMWINDOWATTRIBUTE(33),
                        &round as *const i32 as *const c_void,
                        4,
                    );
                }
            }
        }
        CallNextHookEx(Some(HHOOK::default()), code, wp, lp)
    }
}

fn free_style(st: MenuStyle) {
    unsafe {
        for f in [st.font, st.icons, st.chevron] {
            let _ = DeleteObject(HGDIOBJ(f.0));
        }
    }
}

impl Drop for ModernMenu {
    fn drop(&mut self) {
        if let Some(h) = self.hook.take() {
            unsafe {
                let _ = windows::Win32::UI::WindowsAndMessaging::UnhookWindowsHookEx(h);
            }
        }
        MENU_STYLE.with(|m| {
            if let Some(st) = m.borrow_mut().take() {
                free_style(st);
            }
        });
        unsafe {
            let _ = DeleteObject(HGDIOBJ(self.brush.0));
        }
        self.items.clear();
    }
}

/// WM_MEASUREITEM for a menu: true when it was one of ours.
pub fn measure_menu_item(lp: LPARAM) -> bool {
    use windows::Win32::UI::Controls::{MEASUREITEMSTRUCT, ODT_MENU};
    let mis = unsafe { &mut *(lp.0 as *mut MEASUREITEMSTRUCT) };
    if mis.CtlType != ODT_MENU || mis.itemData == 0 {
        return false;
    }
    MENU_STYLE.with(|m| {
        let m = m.borrow();
        let Some(st) = m.as_ref() else { return false };
        let item = unsafe { &*(mis.itemData as *const MenuItemData) };
        let px = |v: f32| (v * st.s).round() as i32;
        if item.separator {
            mis.itemWidth = px(16.0) as u32;
            mis.itemHeight = px(7.0) as u32;
            return true;
        }
        let w = unsafe {
            let dc = CreateCompatibleDC(None);
            let old = SelectObject(dc, HGDIOBJ(st.font.0));
            let w = text_width(dc, &item.text);
            SelectObject(dc, old);
            let _ = DeleteDC(dc);
            w
        };
        // Icon column, text, then room for the chevron. Windows adds the check-mark width
        // itself; it is taken back here.
        let check = unsafe { windows::Win32::UI::WindowsAndMessaging::GetSystemMetrics(windows::Win32::UI::WindowsAndMessaging::SM_CXMENUCHECK) };
        mis.itemWidth = (px(34.0) + w + px(30.0) - check).max(px(120.0)) as u32;
        mis.itemHeight = px(24.0) as u32;
        true
    })
}

/// WM_DRAWITEM for a menu: true when it was one of ours.
pub fn draw_menu_item(lp: LPARAM) -> bool {
    use windows::Win32::Graphics::Gdi::{BitBlt, ExcludeClipRect, SRCCOPY};
    use windows::Win32::UI::Controls::{DRAWITEMSTRUCT, ODS_CHECKED, ODS_DISABLED, ODS_GRAYED, ODS_SELECTED, ODT_MENU};
    let dis = unsafe { &*(lp.0 as *const DRAWITEMSTRUCT) };
    if dis.CtlType != ODT_MENU || dis.itemData == 0 {
        return false;
    }
    MENU_STYLE.with(|m| {
        let m = m.borrow();
        let Some(st) = m.as_ref() else { return false };
        let item = unsafe { &*(dis.itemData as *const MenuItemData) };
        let px = |v: f32| (v * st.s).round() as i32;
        let rc = dis.rcItem;
        let (w, h) = (rc.right - rc.left, rc.bottom - rc.top);
        if w <= 0 || h <= 0 {
            return true;
        }
        let disabled = dis.itemState.0 & (ODS_DISABLED.0 | ODS_GRAYED.0) != 0;
        let selected = dis.itemState.0 & ODS_SELECTED.0 != 0 && !disabled && !item.separator;
        let checked = dis.itemState.0 & ODS_CHECKED.0 != 0;
        unsafe {
            // Drawn into a bitmap first: the rounded highlight is antialiased there.
            let dc = CreateCompatibleDC(Some(dis.hDC));
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
            let Ok(bmp) = CreateDIBSection(Some(dc), &bmi, DIB_RGB_COLORS, &mut bits, None, 0) else {
                let _ = DeleteDC(dc);
                return true;
            };
            let old_b = SelectObject(dc, HGDIOBJ(bmp.0));
            let pix = std::slice::from_raw_parts_mut(bits as *mut u32, (w * h) as usize);
            let bgr = |c: COLORREF| {
                let (r, g, b) = split(c);
                (r as u32) << 16 | (g as u32) << 8 | b as u32
            };
            pix.fill(bgr(st.bg));
            if item.separator {
                let y = h / 2;
                let c = bgr(st.line);
                for x in px(1.0)..w - px(1.0) {
                    pix[(y * w + x) as usize] = c;
                }
            } else if selected {
                // Rounded highlight, 4 px in from the sides and 1 px from the rows around it.
                let (x0, y0, x1, y1) = (px(4.0) as f32, px(1.0) as f32, (w - px(4.0)) as f32, (h - px(1.0)) as f32);
                let r = 4.0 * st.s;
                let (br, bg_, bb) = split(st.bg);
                let (hr, hg, hb) = split(st.hover);
                for y in 0..h {
                    for x in 0..w {
                        let (fx, fy) = (x as f32 + 0.5, y as f32 + 0.5);
                        let qx = (x0 + r - fx).max(fx - (x1 - r)).max(0.0);
                        let qy = (y0 + r - fy).max(fy - (y1 - r)).max(0.0);
                        let outside = (qx * qx + qy * qy).sqrt() - r;
                        let inside = (x0 - fx).max(fx - x1).max(y0 - fy).max(fy - y1);
                        let d = if qx > 0.0 && qy > 0.0 { outside } else { inside };
                        let a = (0.5 - d).clamp(0.0, 1.0);
                        if a > 0.0 {
                            let mixc = |b: u8, f: u8| (b as f32 + (f as f32 - b as f32) * a).round() as u32;
                            pix[(y * w + x) as usize] = mixc(br, hr) << 16 | mixc(bg_, hg) << 8 | mixc(bb, hb);
                        }
                    }
                }
            }
            if !item.separator {
                SetBkMode(dc, TRANSPARENT);
                let fg = if disabled { st.disabled } else { st.text };
                SetTextColor(dc, fg);
                // Icon column: the check mark when checked, else the item's icon.
                let mark = if checked { Some(glyph::CHECK) } else { item.glyph };
                if mark == Some(glyph::EARBUDS) {
                    // Drawn, not a font glyph: blended in the text colour.
                    let n = px(16.0);
                    let (x0, y0) = (px(9.0), (h - n) / 2);
                    let (fr, fg_, fb) = split(fg);
                    for (i, a) in crate::gui::earbuds_icon(n, true, true).into_iter().enumerate() {
                        let (x, y) = (x0 + i as i32 % n, y0 + i as i32 / n);
                        if a == 0 || y < 0 || y >= h {
                            continue;
                        }
                        let d = &mut pix[(y * w + x) as usize];
                        let mixc = |sh: u32, f: u8| {
                            let b = ((*d >> sh) & 0xFF) as f32;
                            (b + (f as f32 - b) * a as f32 / 255.0).round() as u32
                        };
                        *d = mixc(16, fr) << 16 | mixc(8, fg_) << 8 | mixc(0, fb);
                    }
                } else if let Some(g) = mark {
                    let g = if g == glyph::DASHBOARD && !has_fluent_icons() { glyph::DASHBOARD_MDL2 } else { g };
                    let old = SelectObject(dc, HGDIOBJ(st.icons.0));
                    let mut r = RECT { left: px(9.0), top: 0, right: px(9.0) + px(16.0), bottom: h };
                    draw_text(dc, &g.to_string(), &mut r, DT_CENTER | DT_VCENTER | DT_SINGLELINE);
                    SelectObject(dc, old);
                }
                let old = SelectObject(dc, HGDIOBJ(st.font.0));
                let mut r = RECT { left: px(34.0), top: 0, right: w - px(22.0), bottom: h };
                draw_text(dc, &item.text, &mut r, DT_VCENTER | DT_SINGLELINE | windows::Win32::Graphics::Gdi::DT_END_ELLIPSIS);
                SelectObject(dc, old);
                if item.popup {
                    let old = SelectObject(dc, HGDIOBJ(st.chevron.0));
                    let mut r = RECT { left: w - px(22.0), top: 0, right: w - px(9.0), bottom: h };
                    draw_text(dc, &glyph::RIGHT.to_string(), &mut r, windows::Win32::Graphics::Gdi::DT_RIGHT | DT_VCENTER | DT_SINGLELINE);
                    SelectObject(dc, old);
                }
            }
            let _ = windows::Win32::Graphics::Gdi::GdiFlush();
            let _ = BitBlt(dis.hDC, rc.left, rc.top, w, h, Some(dc), 0, 0, SRCCOPY);
            SelectObject(dc, old_b);
            let _ = DeleteObject(HGDIOBJ(bmp.0));
            let _ = DeleteDC(dc);
            // Keeps Windows from drawing its own submenu arrow over ours.
            ExcludeClipRect(dis.hDC, rc.left, rc.top, rc.right, rc.bottom);
        }
        true
    })
}
