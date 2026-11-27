//! Isolated hybrid layout experiment: three native tray anchors, one external
//! click-through layered window. No settings, polling, installer or Explorer injection.
use batteryhub::{DeviceKind, ui};
use windows::Win32::Foundation::{COLORREF, HWND, LPARAM, LRESULT, POINT, RECT, SIZE, WPARAM};
use windows::Win32::Graphics::Gdi::*;
use windows::Win32::System::LibraryLoader::GetModuleHandleW;
use windows::Win32::UI::HiDpi::{DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2, GetDpiForSystem, GetSystemMetricsForDpi, SetProcessDpiAwarenessContext};
use windows::Win32::UI::Shell::{NIF_ICON, NIF_TIP, NIM_ADD, NIM_DELETE, NIM_MODIFY, NOTIFYICONDATAW, NOTIFYICONIDENTIFIER, Shell_NotifyIconW, Shell_NotifyIconGetRect};
use windows::Win32::UI::WindowsAndMessaging::*;
use windows::core::w;

unsafe extern "system" fn proc(hwnd: HWND, msg: u32, wp: WPARAM, lp: LPARAM) -> LRESULT {
    unsafe {
        if msg == WM_CLOSE { PostQuitMessage(0); return LRESULT(0); }
        if msg == WM_NCHITTEST { return LRESULT(HTTRANSPARENT as isize); }
        DefWindowProcW(hwnd, msg, wp, lp)
    }
}

struct Anchor { data: NOTIFYICONDATAW, marker: HICON }

fn rect_of(a: &Anchor) -> Option<RECT> {
    let id = NOTIFYICONIDENTIFIER {
        cbSize: size_of::<NOTIFYICONIDENTIFIER>() as u32, hWnd: a.data.hWnd,
        uID: a.data.uID, ..Default::default()
    };
    unsafe { Shell_NotifyIconGetRect(&id).ok() }
}

fn layout(anchors: &[Anchor], slot: i32) -> Option<(i32,i32,i32,i32)> {
    if anchors.len() != 3 || slot <= 0 { return None; }
    unsafe {
        let bar = FindWindowW(w!("Shell_TrayWnd"), None).ok()?;
        if !IsWindowVisible(bar).as_bool() { return None; }
        let mut b = RECT::default();
        GetWindowRect(bar, &mut b).ok()?;
        let height = b.bottom - b.top;
        if height < 24 || height > slot * 5 || b.right - b.left < height * 4 { return None; }
        let mut rs: Vec<RECT> = anchors.iter().map(rect_of).collect::<Option<Vec<_>>>()?;
        rs.sort_by_key(|r| r.left);
        if rs.iter().any(|r| r.left < b.left || r.right > b.right || r.top < b.top || r.bottom > b.bottom
            || r.right <= r.left || r.bottom <= r.top || r.right-r.left > slot*3 || r.bottom-r.top > height) {
            return None;
        }
        // Only join our own adjacent anchors. An icon between them invalidates the span.
        let c = |r: &RECT| (r.left+r.right)/2;
        let a = c(&rs[1])-c(&rs[0]);
        let d = c(&rs[2])-c(&rs[1]);
        if a < slot || d < slot || a > slot*5/2 || d > slot*5/2 || (a-d).abs() > 2 ||
            rs.windows(2).any(|p| p[0].right > p[1].left || (p[0].top-p[1].top).abs() > 2) {
            return None;
        }
        let x = rs[0].left;
        let width = rs[2].right - x;
        if width < slot * 4 || width > slot * 8 { return None; }
        // Do not draw over foreground full-screen apps.
        let fg = GetForegroundWindow();
        let mut f = RECT::default();
        if !fg.0.is_null() && fg != bar && GetWindowRect(fg, &mut f).is_ok() &&
            f.left <= x && f.right >= x+width && f.top <= b.top && f.bottom >= b.bottom {
            return None;
        }
        Some((x,b.top+1,width,height-2))
    }
}

fn set_anchor_icons(anchors: &[Anchor], blank: Option<HICON>) -> bool {
    let mut ok = true;
    for a in anchors {
        let mut d = a.data;
        d.uFlags = NIF_ICON;
        d.hIcon = blank.unwrap_or(a.marker);
        ok &= unsafe { Shell_NotifyIconW(NIM_MODIFY, &d).as_bool() };
    }
    ok
}

fn paint(hwnd: HWND, geom: (i32,i32,i32,i32), color: COLORREF, slot: i32) -> bool {
    let (x,y,width,height) = geom;
    unsafe {
        let dc = CreateCompatibleDC(None);
        let bmi = BITMAPINFO {
            bmiHeader: BITMAPINFOHEADER {
                biSize: size_of::<BITMAPINFOHEADER>() as u32, biWidth: width, biHeight: -height,
                biPlanes: 1, biBitCount: 32, biCompression: BI_RGB.0, ..Default::default()
            }, ..Default::default()
        };
        let mut bits: *mut core::ffi::c_void = std::ptr::null_mut();
        let Ok(bmp) = CreateDIBSection(Some(dc), &bmi, DIB_RGB_COLORS, &mut bits, None, 0) else {
            let _ = DeleteDC(dc); return false;
        };
        let old = SelectObject(dc, HGDIOBJ(bmp.0));
        let px = std::slice::from_raw_parts_mut(bits as *mut u32, (width*height) as usize);
        px.fill(0);
        SetBkMode(dc, TRANSPARENT);
        SetTextColor(dc, ui::rgb(255,255,255));
        let glyph_f = ui::font((slot*9/10).max(12), 400, ui::icon_font_face());
        let number_f = ui::font((slot*3/4).max(10), 500, "Segoe UI");
        let flags = DT_CENTER | DT_VCENTER | DT_SINGLELINE;
        for (i, kind, text) in [(0,DeviceKind::Headset,"85%"), (1,DeviceKind::Mouse,"72%")] {
            let l = width*i/2;
            let r = width*(i+1)/2;
            let mut icon = RECT {left:l, top:0, right:r, bottom:height/2+2};
            let mut num = RECT {left:l, top:height/2-2, right:r, bottom:height};
            SelectObject(dc,HGDIOBJ(glyph_f.0));
            ui::draw_text(dc,&kind.glyph().to_string(),&mut icon,flags);
            SelectObject(dc,HGDIOBJ(number_f.0));
            ui::draw_text(dc,text,&mut num,flags);
        }
        let _ = GdiFlush();
        let (r,g,b) = ui::split(color);
        for p in px.iter_mut() {
            let a = (*p & 255).max((*p>>8)&255).max((*p>>16)&255);
            *p = (a<<24) | (((r as u32*a)/255)<<16) | (((g as u32*a)/255)<<8) | ((b as u32*a)/255);
        }
        let pt = POINT{x,y};
        let src = POINT{x:0,y:0};
        let sz = SIZE{cx:width,cy:height};
        let blend = BLENDFUNCTION{BlendOp:AC_SRC_OVER as u8, BlendFlags:0, SourceConstantAlpha:255, AlphaFormat:AC_SRC_ALPHA as u8};
        let ok = UpdateLayeredWindow(hwnd,None,Some(&pt),Some(&sz),Some(dc),Some(&src),COLORREF(0),Some(&blend),ULW_ALPHA).is_ok();
        SelectObject(dc,old);
        let _=DeleteObject(HGDIOBJ(glyph_f.0));
        let _=DeleteObject(HGDIOBJ(number_f.0));
        let _=DeleteObject(HGDIOBJ(bmp.0));
        let _=DeleteDC(dc);
        ok
    }
}

fn main() {
    unsafe {
        let _ = SetProcessDpiAwarenessContext(DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2);
        let inst = GetModuleHandleW(None).unwrap_or_default();
        let class = w!("BatteryHub.HybridPreview");
        let wc = WNDCLASSEXW{cbSize:size_of::<WNDCLASSEXW>() as u32,lpfnWndProc:Some(proc),hInstance:inst.into(),lpszClassName:class,..Default::default()};
        if RegisterClassExW(&wc)==0 { return; }
        let Ok(owner)=CreateWindowExW(WS_EX_TOOLWINDOW,class,w!("BatteryHub Hybrid Preview"),WS_POPUP,0,0,0,0,None,None,Some(inst.into()),None) else {return;};
        let Ok(overlay)=CreateWindowExW(WS_EX_LAYERED|WS_EX_TRANSPARENT|WS_EX_NOACTIVATE|WS_EX_TOOLWINDOW|WS_EX_TOPMOST,class,w!("BatteryHub Hybrid Overlay"),WS_POPUP,0,0,0,0,None,None,Some(inst.into()),None) else {let _=DestroyWindow(owner); return;};
        let light = ui::taskbar_is_light();
        let color=if light {ui::rgb(20,20,20)} else {ui::rgb(255,255,255)};
        let slot=GetSystemMetricsForDpi(SM_CXSMICON,GetDpiForSystem()).clamp(16,64);
        // Monochrome transparent icon: AND all ones, XOR all zero.
        let bytes=(((slot as usize+15)/16)*2)*slot as usize;
        let and=vec![255u8;bytes]; let xor=vec![0u8;bytes];
        let Ok(blank)=CreateIcon(Some(inst.into()),slot,slot,1,1,and.as_ptr(),xor.as_ptr()) else {let _=DestroyWindow(overlay);let _=DestroyWindow(owner);return;};
        let mut anchors=Vec::new();
        for id in 1..=3u32 {
            let Some(marker)=ui::number_icon(&id.to_string(),color,-1,slot,light) else {continue;};
            let mut data=NOTIFYICONDATAW{cbSize:size_of::<NOTIFYICONDATAW>() as u32,hWnd:owner,uID:id,uFlags:NIF_ICON|NIF_TIP,hIcon:marker,..Default::default()};
            ui::fill_wide(&mut data.szTip,&format!("Hybrid PREVIEW anchor {id}"));
            if Shell_NotifyIconW(NIM_ADD,&data).as_bool() {anchors.push(Anchor{data,marker});} else {let _=DestroyIcon(marker);}
        }
        println!("Hybrid preview: {} anchors. Drag numbered icons together to the visible tray.",anchors.len());
        println!("Only when adjacent: show external widget with synthetic 85% and 72%.");
        println!("Press ENTER to remove all preview icons and the overlay.");
        let raw=owner.0 as isize;
        std::thread::spawn(move||{let mut s=String::new();let _=std::io::stdin().read_line(&mut s);let _=PostMessageW(Some(HWND(raw as *mut core::ffi::c_void)),WM_CLOSE,WPARAM(0),LPARAM(0));});
        SetTimer(Some(owner),1,250,None);
        let mut active=None;
        let mut previous=None;
        let mut last_rects = Vec::new();
        let mut msg=MSG::default();
        while GetMessageW(&mut msg,None,0,0).0>0 {
            if msg.message==WM_TIMER && msg.hwnd==owner {
                let rects: Vec<_> = anchors.iter().map(|a| rect_of(a).map(|r| (r.left,r.top,r.right,r.bottom))).collect();
                if rects != last_rects {
                    println!("Anchor rectangles: {rects:?}");
                    last_rects = rects;
                }
                let candidate=layout(&anchors,slot);
                // Require stable geometry before displaying. Hide immediately when anchors move.
                if candidate!=active && active.is_some() {
                    let _=ShowWindow(overlay,SW_HIDE);
                    set_anchor_icons(&anchors,None);
                    active=None;
                    println!("Overlay hidden; anchors restored.");
                }
                if let Some(g)=candidate {
                    if active.is_none() && previous==Some(g) && paint(overlay,g,color,slot) {
                        if set_anchor_icons(&anchors,Some(blank)) {
                            let _=ShowWindow(overlay,SW_SHOWNOACTIVATE);
                            active=Some(g);
                            println!("Overlay active: x={} y={} width={} height={}",g.0,g.1,g.2,g.3);
                        } else {set_anchor_icons(&anchors,None);}
                    }
                }
                previous=candidate;
            }
            let _=TranslateMessage(&msg);
            DispatchMessageW(&msg);
        }
        let _=KillTimer(Some(owner),1);
        let _=ShowWindow(overlay,SW_HIDE);
        for a in anchors {let _=Shell_NotifyIconW(NIM_DELETE,&a.data);let _=DestroyIcon(a.marker);}
        let _=DestroyIcon(blank);
        let _=DestroyWindow(overlay);
        let _=DestroyWindow(owner);
    }
}
