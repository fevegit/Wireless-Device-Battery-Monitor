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

// Hand-hinted monochrome bitmaps at the actual 16px tray size. No text
// antialiasing at this size: every stroke is an integral physical pixel.
const DIGITS: [[u8; 7]; 10] = [
    [14,17,19,21,25,17,14], [4,12,4,4,4,4,14], [14,17,1,2,4,8,31],
    [30,1,1,14,1,1,30], [2,6,10,18,31,2,2], [31,16,16,30,1,1,30],
    [14,16,16,30,17,17,14], [31,1,2,4,8,8,8], [14,17,17,14,17,17,14],
    [14,17,17,15,1,1,14],
];
const SMALL: [[u8; 5]; 10] = [
    [7,5,5,5,7], [2,6,2,2,7], [7,1,7,4,7], [7,1,7,1,7], [5,5,7,1,1],
    [7,4,7,1,7], [7,4,7,5,7], [7,1,2,2,2], [7,5,7,5,7], [7,5,7,1,7],
];

fn stamp(p: &mut [u32; 256], rows: &[u8], width: usize, x: usize, y: usize, color: u32) {
    for (dy, row) in rows.iter().enumerate() {
        for dx in 0..width {
            if row & (1 << (width - 1 - dx)) != 0 && x + dx < 16 && y + dy < 16 {
                p[(y + dy) * 16 + x + dx] = color;
            }
        }
    }
}

fn pixel_icon(kind: DeviceKind, level: i32, size: i32, color: windows::Win32::Foundation::COLORREF) -> Option<HICON> {
    use windows::Win32::Graphics::Gdi::*;
    let (r,g,b) = ui::split(color);
    let ink = 0xff000000 | ((r as u32) << 16) | ((g as u32) << 8) | b as u32;
    let mut p = [0u32; 256];
    let glyph: [u8; 7] = match kind {
        DeviceKind::Headset => [0b0011100,0b0100010,0b1000001,0b1000001,0b1100011,0b1100011,0b0100010],
        DeviceKind::Mouse => [0b0011100,0b0101010,0b1001001,0b1111111,0b1000001,0b1000001,0b0111110],
        DeviceKind::Keyboard => [0,0b1111111,0b1000001,0b1010101,0b1000001,0b1111111,0],
        _ => [0,0b1111111,0b1000001,0b1000001,0b1000001,0b1111111,0],
    };
    stamp(&mut p, &glyph, 7, 4, 0, ink);
    let digits = level.clamp(0, 100).to_string();
    let (w, step, y) = if digits.len() == 3 { (3, 4, 9) } else { (5, 6, 8) };
    let left = (16 - (digits.len() * step - 1)) / 2;
    for (i, d) in digits.bytes().enumerate() {
        let n = (d - b'0') as usize;
        let rows: &[u8] = if w == 3 { &SMALL[n] } else { &DIGITS[n] };
        stamp(&mut p, rows, w, left + i * step, y, ink);
    }
    if size < 16 || size > 256 { return None; }
    unsafe {
        let bmi = BITMAPINFO {
            bmiHeader: BITMAPINFOHEADER {
                biSize: size_of::<BITMAPINFOHEADER>() as u32,
                biWidth: size, biHeight: -size, biPlanes: 1, biBitCount: 32,
                biCompression: BI_RGB.0, ..Default::default()
            }, ..Default::default()
        };
        let mut bits: *mut core::ffi::c_void = std::ptr::null_mut();
        let bmp = CreateDIBSection(None, &bmi, DIB_RGB_COLORS, &mut bits, None, 0).ok()?;
        let px = std::slice::from_raw_parts_mut(bits as *mut u32, (size * size) as usize);
        for y in 0..size as usize {
            for x in 0..size as usize {
                px[y * size as usize + x] = p[(y * 16 / size as usize) * 16 + x * 16 / size as usize];
            }
        }
        let mask = CreateBitmap(size, size, 1, 1, None);
        let info = ICONINFO { fIcon: true.into(), hbmColor: bmp, hbmMask: mask, ..Default::default() };
        let icon = CreateIconIndirect(&info).ok();
        let _ = DeleteObject(HGDIOBJ(bmp.0));
        let _ = DeleteObject(HGDIOBJ(mask.0));
        icon
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
        let args: Vec<String> = std::env::args().collect();
        let numeric = args.iter().any(|arg| arg == "--numbers");
        let hires = args.iter().any(|arg| arg == "--hires");
        let original = args.iter().any(|arg| arg == "--original");
        let mode = if numeric { "numbers" } else if hires { "hires" } else if original { "original" } else { "pixel" };
        let mut icons = Vec::new();
        for (id, kind, level, name, color) in [
            (1, DeviceKind::Headset, 85, "PREVIEW only: headset 85%", normal),
            (2, DeviceKind::Mouse, 72, "PREVIEW only: mouse 72%", normal),
            (3, DeviceKind::Keyboard, 100, "PREVIEW only: keyboard 100% (charging)", ui::charging_color(light)),
        ] {
            let text = level.to_string();
            let icon = if numeric {
                ui::number_icon(&text, color, level, size, light)
            } else if hires || original {
                ui::device_number_icon(&text, color, level, if hires { size * 2 } else { size }, light, kind.glyph())
            } else {
                pixel_icon(kind, level, size, color)
                    .or_else(|| ui::device_number_icon(&text, color, level, size, light, kind.glyph()))
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
        println!("Native tray preview: {mode} mode, {} px slot, {} icons, synthetic values only.", size, icons.len());
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
