//! Isolated hybrid layout experiment: five native tray anchors (one guard slot), one external
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
    if anchors.len() != 5 || slot <= 0 { return None; }
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
        if a < slot || a > slot*5/2 ||
            rs.windows(2).any(|p| (c(&p[1])-c(&p[0])-a).abs() > 2 ||
                (p[0].right-p[1].left).abs() > 2 || (p[0].top-p[1].top).abs() > 2) {
            return None;
        }
        // Personal-XAML can coexist with this test and the shell's chevron
        // may be drawn over the leftmost reported anchor. Keep that entire
        // slot free of overlay pixels; only render in the remaining four.
        let x = rs[1].left;
        let width = rs[4].right - x;
        if width < slot * 6 || width > slot * 10 { return None; }
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
        let mut bits: *mut core::ffi::c_void = std::ptr::null_mut();
        let mut out = Mask { w: 0, h: 0, a: Vec::new() };
        if let Ok(bmp) = CreateDIBSection(Some(dc), &bmi, DIB_RGB_COLORS, &mut bits, None, 0) {
            let old_b = SelectObject(dc, HGDIOBJ(bmp.0));
            let px = std::slice::from_raw_parts_mut(bits as *mut u32, (w * h) as usize);
            px.fill(if dark_on_light { 0xFFFF_FFFF } else { 0 });
            SetBkMode(dc, TRANSPARENT);
            SetTextColor(dc, if dark_on_light { ui::rgb(0, 0, 0) } else { ui::rgb(255, 255, 255) });
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

// The static renderer below ports the ink-mask and font routines from the
// published experimental XAML contribution. Only presentation is external.
fn paint(hwnd: HWND, geom: (i32,i32,i32,i32), _color: COLORREF, _slot: i32) -> bool {
    let (x,y,width,height) = geom;
    unsafe {
        let bar = FindWindowW(w!("Shell_TrayWnd"), None).ok();
        let dpi = bar.map(|b| windows::Win32::UI::HiDpi::GetDpiForWindow(b)).unwrap_or(96).max(96);
        let scale = dpi as f32 / 96.0;
        let px = |v: f32| (v * scale).round() as i32;
        let light = ui::taskbar_is_light();
        let fg = if light { ui::rgb(0,0,0) } else { ui::rgb(255,255,255) };
        let icons = make_font(px(16.0),400,"Segoe Fluent Icons","Segoe MDL2 Assets",0);
        let text = make_font(px(13.0),400,"Segoe UI Variable Text","Segoe UI",px(12.0));
        let bolt = make_font(px(11.0),400,"Segoe Fluent Icons","Segoe MDL2 Assets",0);
        let pieces = [
            (mask(&DeviceKind::Headset.glyph().to_string(),icons,light),fg,px(5.0)),
            (mask("49%",text,light),fg,px(14.0)),
            (mask(&DeviceKind::Mouse.glyph().to_string(),icons,light),fg,px(5.0)),
            (mask("95%",text,light),fg,px(2.0)),
            (mask("\u{E945}",bolt,light),ui::charging_color(light),0),
        ];
        for f in [icons,text,bolt] {let _=DeleteObject(HGDIOBJ(f.0));}
        let content: i32 = pieces.iter().map(|(m,_,gap)|m.w+gap).sum();
        if content > width || pieces.iter().any(|(m,_,_)|m.w==0 || m.h>height) {
            println!("XAML renderer content {}px does not fit {}px or a mask is empty",content,width);
            return false;
        }
        let mut pixels=vec![0x0100_0000u32;(width*height) as usize];
        let mut left=(width-content)/2;
        for (m,c,gap) in &pieces {
            let top=(height-m.h)/2;
            let (r,g,b)=ui::split(*c);
            for yy in 0..m.h {for xx in 0..m.w {
                let a=m.a[(yy*m.w+xx) as usize] as u32;
                if a==0 {continue;}
                let d=&mut pixels[((top+yy)*width+left+xx) as usize];
                let inv=255-a;
                let ch=|src:u8,shift:u32| ((src as u32*a+((*d>>shift)&255)*inv)/255)&255;
                let na=(a+((*d>>24)&255)*inv/255).min(255);
                *d=na<<24|ch(r,16)<<16|ch(g,8)<<8|ch(b,0);
            }}
            left+=m.w+gap;
        }
        let screen=GetDC(None);
        let dc=CreateCompatibleDC(Some(screen));
        let bmi=BITMAPINFO{
            bmiHeader:BITMAPINFOHEADER{
                biSize:size_of::<BITMAPINFOHEADER>() as u32,biWidth:width,biHeight:-height,
                biPlanes:1,biBitCount:32,biCompression:BI_RGB.0,..Default::default()
            },..Default::default()
        };
        let mut bits:*mut core::ffi::c_void=std::ptr::null_mut();
        let Ok(bmp)=CreateDIBSection(Some(dc),&bmi,DIB_RGB_COLORS,&mut bits,None,0) else {
            let _=DeleteDC(dc);let _=ReleaseDC(None,screen);return false;
        };
        let old=SelectObject(dc,HGDIOBJ(bmp.0));
        std::ptr::copy_nonoverlapping(pixels.as_ptr(),bits as *mut u32,pixels.len());
        let pt=POINT{x,y};
        let src=POINT::default();
        let sz=SIZE{cx:width,cy:height};
        let blend=BLENDFUNCTION{BlendOp:AC_SRC_OVER as u8,BlendFlags:0,SourceConstantAlpha:255,AlphaFormat:AC_SRC_ALPHA as u8};
        let result=UpdateLayeredWindow(hwnd,Some(screen),Some(&pt),Some(&sz),Some(dc),Some(&src),COLORREF(0),Some(&blend),ULW_ALPHA);
        let ink=pixels.iter().filter(|&&p|p>>24>1).count();
        println!("XAML mask renderer: dpi={dpi}, content={content}px, slot={width}px, ink={ink}, result={result:?}");
        SelectObject(dc,old);
        let _=DeleteObject(HGDIOBJ(bmp.0));
        let _=DeleteDC(dc);
        let _=ReleaseDC(None,screen);
        ink>0 && result.is_ok()
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
        for id in 1..=5u32 {
            let Some(marker)=ui::number_icon(&id.to_string(),color,-1,slot,light) else {continue;};
            let mut data=NOTIFYICONDATAW{cbSize:size_of::<NOTIFYICONDATAW>() as u32,hWnd:owner,uID:id,uFlags:NIF_ICON|NIF_TIP,hIcon:marker,..Default::default()};
            ui::fill_wide(&mut data.szTip,&format!("Hybrid PREVIEW anchor {id}"));
            if Shell_NotifyIconW(NIM_ADD,&data).as_bool() {anchors.push(Anchor{data,marker});} else {let _=DestroyIcon(marker);}
        }
        println!("Hybrid preview: {} anchors. Drag numbered icons together to the visible tray.",anchors.len());
        println!("Only when adjacent: leave the leftmost anchor clear for Windows, then show 49% and 95% (charging).");
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
                        let raised = SetWindowPos(overlay,Some(HWND_TOPMOST),g.0,g.1,g.2,g.3,SWP_NOACTIVATE|SWP_SHOWWINDOW);
                        println!("Raise overlay: {raised:?}; visible={}",IsWindowVisible(overlay).as_bool());
                        if raised.is_ok() && IsWindowVisible(overlay).as_bool() && set_anchor_icons(&anchors,Some(blank)) {
                            active=Some(g);
                            println!("Overlay active: x={} y={} width={} height={}",g.0,g.1,g.2,g.3);
                        } else {
                            let _=ShowWindow(overlay,SW_HIDE);
                            set_anchor_icons(&anchors,None);
                        }
                    }
                }
                if active.is_some() && candidate==active {
                    // Explorer can raise its own topmost window after shell layout changes.
                    let _=SetWindowPos(overlay,Some(HWND_TOPMOST),0,0,0,0,SWP_NOMOVE|SWP_NOSIZE|SWP_NOACTIVATE);
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
