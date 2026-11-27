//! Standalone visual experiment. No BatteryHub settings, history, HID polling,
//! updater, autostart, shared mutex, or taskbar hooks. Synthetic levels only.
use batteryhub::{DeviceKind, ui};
use windows::Win32::Foundation::{HWND, LPARAM, LRESULT, WPARAM};
use windows::Win32::System::LibraryLoader::GetModuleHandleW;
use windows::Win32::UI::HiDpi::{
    DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2, GetDpiForSystem, GetSystemMetricsForDpi,
    SetProcessDpiAwarenessContext,
};
use windows::Win32::UI::Shell::{
    NIF_ICON, NIF_TIP, NIM_ADD, NIM_DELETE, NOTIFYICONDATAW, Shell_NotifyIconW,
};
use windows::Win32::UI::WindowsAndMessaging::*;
use windows::core::w;

unsafe extern "system" fn window_proc(hwnd: HWND, msg: u32, wp: WPARAM, lp: LPARAM) -> LRESULT {
    unsafe {
        if msg == WM_CLOSE || msg == WM_DESTROY {
            PostQuitMessage(0);
            return LRESULT(0);
        }
        DefWindowProcW(hwnd, msg, wp, lp)
    }
}

fn main() {
    unsafe {
        let _ = SetProcessDpiAwarenessContext(DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2);
        let hinst = GetModuleHandleW(None).unwrap_or_default();
        let class = w!("BatteryHub.NativeTrayPreview");
        let wc = WNDCLASSEXW {
            cbSize: size_of::<WNDCLASSEXW>() as u32,
            lpfnWndProc: Some(window_proc),
            hInstance: hinst.into(),
            lpszClassName: class,
            ..Default::default()
        };
        if RegisterClassExW(&wc) == 0 {
            eprintln!("Could not register preview window.");
            return;
        }
        let Ok(hwnd) = CreateWindowExW(
            WS_EX_TOOLWINDOW, class, w!("BatteryHub Native Tray Preview"), WS_POPUP,
            0, 0, 0, 0, None, None, Some(hinst.into()), None,
        ) else {
            eprintln!("Could not create preview window.");
            return;
        };
        let light = ui::taskbar_is_light();
        let normal = if light { ui::rgb(20, 20, 20) } else { ui::rgb(255, 255, 255) };
        let size = GetSystemMetricsForDpi(SM_CXSMICON, GetDpiForSystem());
        let numeric = std::env::args().any(|arg| arg == "--numbers");
        let mut icons = Vec::new();
        for (id, kind, level, name, color) in [
            (1, DeviceKind::Headset, 85, "PREVIEW only: headset 85%", normal),
            (2, DeviceKind::Mouse, 72, "PREVIEW only: mouse 72%", normal),
            (3, DeviceKind::Keyboard, 100, "PREVIEW only: keyboard 100% (charging)", ui::charging_color(light)),
        ] {
            let text = level.to_string();
            let icon = if numeric {
                ui::number_icon(&text, color, level, size, light)
            } else {
                ui::device_number_icon(&text, color, level, size, light, kind.glyph())
            };
            let Some(icon) = icon else {
                eprintln!("Could not render preview icon {id}");
                continue;
            };
            let mut data = NOTIFYICONDATAW {
                cbSize: size_of::<NOTIFYICONDATAW>() as u32,
                hWnd: hwnd,
                uID: id,
                uFlags: NIF_ICON | NIF_TIP,
                hIcon: icon,
                ..Default::default()
            };
            ui::fill_wide(&mut data.szTip, name);
            if Shell_NotifyIconW(NIM_ADD, &data).as_bool() {
                icons.push((data, icon));
            } else {
                eprintln!("Could not add preview icon {id}");
                let _ = DestroyIcon(icon);
            }
        }
        if icons.is_empty() {
            let _ = DestroyWindow(hwnd);
            return;
        }
        println!("Native tray preview: {} px, {} icons, synthetic values only.", size, icons.len());
        println!("Look in the tray or hidden icons (^). Drag preview icons out if desired.");
        println!("Press ENTER to remove the preview icons and exit.");
        let handle = hwnd.0 as isize;
        std::thread::spawn(move || {
            let mut line = String::new();
            let _ = std::io::stdin().read_line(&mut line);
            let _ = PostMessageW(Some(HWND(handle as *mut core::ffi::c_void)), WM_CLOSE, WPARAM(0), LPARAM(0));
        });
        let mut msg = MSG::default();
        while GetMessageW(&mut msg, None, 0, 0).0 > 0 {
            let _ = TranslateMessage(&msg);
            DispatchMessageW(&msg);
        }
        for (data, icon) in icons {
            let _ = Shell_NotifyIconW(NIM_DELETE, &data);
            let _ = DestroyIcon(icon);
        }
        let _ = DestroyWindow(hwnd);
    }
}
