//! Isolated hybrid layout experiment: four native tray anchors with a read-only overflow-button check, one external
//! click-through layered window. No settings, polling, installer or Explorer injection.
use batteryhub::{DeviceKind, ui};
use windows::Win32::Foundation::{COLORREF, HWND, LPARAM, LRESULT, POINT, RECT, SIZE, WPARAM};
use windows::Win32::Graphics::Gdi::*;
use windows::Win32::System::LibraryLoader::GetModuleHandleW;
use windows::Win32::UI::HiDpi::{DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2, GetDpiForSystem, GetSystemMetricsForDpi, SetProcessDpiAwarenessContext};
use windows::Win32::UI::Shell::{NIF_ICON, NIF_TIP, NIM_ADD, NIM_DELETE, NOTIFYICONDATAW, NOTIFYICONIDENTIFIER, Shell_NotifyIconW, Shell_NotifyIconGetRect};
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

type Geometry = (i32,i32,i32,i32);

fn layout(rects: &[Option<RECT>], slot: i32) -> Option<Geometry> {
    if rects.len() != 4 || slot <= 0 { return None; }
    unsafe {
        let bar = FindWindowW(w!("Shell_TrayWnd"), None).ok()?;
        if !IsWindowVisible(bar).as_bool() { return None; }
        let mut b = RECT::default();
        GetWindowRect(bar, &mut b).ok()?;
        let height = b.bottom - b.top;
        if height < 24 || height > slot * 5 || b.right - b.left < height * 4 { return None; }
        let mut rs: Vec<RECT> = rects.iter().copied().collect::<Option<Vec<_>>>()?;
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
        let x = rs[0].left;
        let width = rs[3].right - x;
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

// Shell_NotifyIconGetRect can return the overflow button's rectangle for a
// hidden icon. Check the actual accessibility element separately before
// drawing. The COM query runs off the preview window's message thread.
fn overflow_worker(
    requests: std::sync::mpsc::Receiver<Geometry>,
    replies: std::sync::mpsc::Sender<(Option<Geometry>,Option<Geometry>)>,
) {
    use windows::Win32::System::Com::{CLSCTX_INPROC_SERVER, COINIT_MULTITHREADED, CoCreateInstance, CoInitializeEx, CoUninitialize};
    use windows::Win32::UI::Accessibility::{CUIAutomation, IUIAutomation, IUIAutomationElement, TreeScope_Descendants};
    unsafe {
        if CoInitializeEx(None,COINIT_MULTITHREADED).is_err() {return;}
        {
            let mut uia:Option<IUIAutomation>=None;
            let mut cached:Option<IUIAutomationElement>=None;
            let mut last_bar=HWND::default();
            let mut last_geom=None;
            let mut last_scan=std::time::Instant::now();
            while let Ok(geom)=requests.recv() {
                let result=(|| -> windows::core::Result<Option<Geometry>> {
                    let bar=FindWindowW(w!("Shell_TrayWnd"),None)?;
                    let mut br=RECT::default();
                    GetWindowRect(bar,&mut br)?;
                    let bounds=|e:&IUIAutomationElement| -> Option<Geometry> {
                        if e.CurrentIsOffscreen().ok()?.as_bool() {return None;}
                        let r=e.CurrentBoundingRectangle().ok()?;
                        if r.left<br.left || r.right>br.right || r.top<br.top || r.bottom>br.bottom ||
                            r.right<=r.left || r.bottom<=r.top || r.right-r.left>80 {return None;}
                        Some((r.left,r.top,r.right,r.bottom))
                    };
                    let matches=|e:&IUIAutomationElement| {
                        let name=e.CurrentName().map(|s|s.to_string().to_lowercase()).unwrap_or_default();
                        let id=e.CurrentAutomationId().map(|s|s.to_string().to_lowercase()).unwrap_or_default();
                        name.contains("hidden icons") || name.contains("iconos ocultos") ||
                        name.contains("iconos escondidos") || id.contains("chevron") || id.contains("overflowbutton")
                    };
                    if bar==last_bar && last_geom==Some(geom) && last_scan.elapsed().as_secs()<10 {
                        if let Some(e)=cached.as_ref() {
                            if matches(e) {
                                if let Some(r)=bounds(e) {return Ok(Some(r));}
                            }
                        }
                    }
                    cached=None;
                    last_bar=bar;
                    last_geom=Some(geom);
                    last_scan=std::time::Instant::now();
                    if uia.is_none() {uia=Some(CoCreateInstance(&CUIAutomation,None,CLSCTX_INPROC_SERVER)?);}
                    let uia=uia.as_ref().unwrap();
                    let root=uia.ElementFromHandle(bar)?;
                    let all=root.FindAll(TreeScope_Descendants,&uia.CreateTrueCondition()?)?;
                    let mut best:Option<Geometry>=None;
                    for i in 0..all.Length()? {
                        let e=all.GetElement(i)?;
                        if !matches(&e) {continue;}
                        if let Some(v)=bounds(&e) {
                            if best.is_none_or(|b|v.0<b.0) {best=Some(v);cached=Some(e);}
                        }
                    }
                    Ok(best)
                })();
                if replies.send((Some(geom),result.ok().flatten())).is_err() {break;}
            }
        }
        CoUninitialize();
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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct DemoState { headset: i32, mouse: i32, charging: bool }
const DEMO_STATES: [DemoState; 5] = [
    DemoState { headset: 49, mouse: 95, charging: true },
    DemoState { headset: 48, mouse: 100, charging: true },
    DemoState { headset: 15, mouse: 100, charging: false },
    DemoState { headset: 9, mouse: 99, charging: false },
    DemoState { headset: 100, mouse: 8, charging: true },
];

fn paint(hwnd: HWND, geom: (i32,i32,i32,i32), _color: COLORREF, _slot: i32, state: DemoState) -> bool {
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
        let low = |v| if v <= 15 { ui::low_color(light) } else { fg };
        let mut pieces = vec![
            (mask(&DeviceKind::Headset.glyph().to_string(),icons,light),fg,px(5.0)),
            (mask(&format!("{}%",state.headset),text,light),low(state.headset),px(14.0)),
            (mask(&DeviceKind::Mouse.glyph().to_string(),icons,light),fg,px(5.0)),
            (mask(&format!("{}%",state.mouse),text,light),low(state.mouse),if state.charging {px(2.0)} else {0}),
        ];
        if state.charging {
            let c=if state.mouse==100 {ui::full_color(light)} else {ui::charging_color(light)};
            pieces.push((mask("\u{E945}",bolt,light),c,0));
        }
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
        // Numbered markers are a deliberate setup-only mode. Normal preview
        // anchors must stay transparent even during capture/foreground changes.
        let setup_anchors=std::env::args().any(|a|a=="--anchors");
        let mut anchors=Vec::new();
        for id in 1..=4u32 {
            let Some(marker)=ui::number_icon(&id.to_string(),color,-1,slot,light) else {continue;};
            let mut data=NOTIFYICONDATAW{cbSize:size_of::<NOTIFYICONDATAW>() as u32,hWnd:owner,uID:id,uFlags:NIF_ICON|NIF_TIP,hIcon:if setup_anchors {marker} else {blank},..Default::default()};
            ui::fill_wide(&mut data.szTip,&format!("Hybrid PREVIEW anchor {id}"));
            if Shell_NotifyIconW(NIM_ADD,&data).as_bool() {anchors.push(Anchor{data,marker});} else {let _=DestroyIcon(marker);}
        }
        println!("Hybrid preview: {} anchors ({}).",anchors.len(),if setup_anchors {"setup markers"} else {"transparent"});
        if setup_anchors {println!("Drag numbered icons together, then press ENTER and restart without --anchors.");}
        else {println!("If the overlay cannot activate, restart with --anchors to arrange the slots.");}
        println!("Four visible adjacent anchors and a verified clear overflow button are required.");
        println!("Press ENTER to remove all preview icons and the overlay.");
        let raw=owner.0 as isize;
        std::thread::spawn(move||{let mut s=String::new();let _=std::io::stdin().read_line(&mut s);let _=PostMessageW(Some(HWND(raw as *mut core::ffi::c_void)),WM_CLOSE,WPARAM(0),LPARAM(0));});
        if !setup_anchors {SetTimer(Some(owner),1,250,None);}
        let cycle=std::env::args().any(|a|a=="--cycle");
        let started=std::time::Instant::now();
        let mut rendered=None;
        if cycle {println!("QA cycle: synthetic battery state changes every 5 seconds.");}
        let mut active=None;
        let mut previous=None;
        let mut last_rects = Vec::new();
        let (tx,rx)=std::sync::mpsc::channel();
        let (request_tx,request_rx)=std::sync::mpsc::channel();
        std::thread::spawn(move||overflow_worker(request_rx,tx));
        let mut probe_pending=false;
        let mut checked=None;
        let mut checked_geom=None;
        let mut checked_at=std::time::Instant::now();
        let mut last_guard=None;
        let mut msg=MSG::default();
        while GetMessageW(&mut msg,None,0,0).0>0 {
            if msg.message==WM_TIMER && msg.hwnd==owner {
                let raw_rects: Vec<_> = anchors.iter().map(rect_of).collect();
                let rects: Vec<_> = raw_rects.iter().map(|r| r.map(|r| (r.left,r.top,r.right,r.bottom))).collect();
                if rects != last_rects {
                    println!("Anchor rectangles: {rects:?}");
                    last_rects = rects;
                }
                let state=DEMO_STATES[if cycle {(started.elapsed().as_secs()/5) as usize % DEMO_STATES.len()} else {0}];
                let geometry=layout(&raw_rects,slot);
                if let Ok((g,r))=rx.try_recv() {
                    probe_pending=false;
                    checked_geom=g;
                    checked=r;
                    checked_at=std::time::Instant::now();
                    if last_guard!=Some((g,r)) {
                        println!("Overflow check: geometry={g:?}, button={r:?}");
                        last_guard=Some((g,r));
                    }
                }
                if geometry.is_some() && !probe_pending &&
                    (checked_geom!=geometry || checked_at.elapsed().as_millis()>=1000) {
                    probe_pending=request_tx.send(geometry.unwrap()).is_ok();
                }
                // Fail closed on an unknown or stale chevron; never cover it.
                let candidate=geometry.filter(|g| {
                    checked_geom==geometry && checked_at.elapsed().as_millis()<2500 &&
                        checked.is_some_and(|r|g.0>=r.2)
                });
                // Require stable geometry before displaying. Hide immediately when anchors move.
                if candidate!=active && active.is_some() {
                    let _=ShowWindow(overlay,SW_HIDE);
                    active=None;
                    rendered=None;
                    println!("Overlay temporarily hidden; anchors remain transparent.");
                }
                if let Some(g)=candidate {
                    if active.is_none() && previous==Some(g) && paint(overlay,g,color,slot,state) {
                        let raised = SetWindowPos(overlay,Some(HWND_TOPMOST),g.0,g.1,g.2,g.3,SWP_NOACTIVATE|SWP_SHOWWINDOW);
                        println!("Raise overlay: {raised:?}; visible={}",IsWindowVisible(overlay).as_bool());
                        if raised.is_ok() && IsWindowVisible(overlay).as_bool() {
                            active=Some(g);
                            rendered=Some(state);
                            println!("Overlay active: x={} y={} width={} height={}",g.0,g.1,g.2,g.3);
                        } else {
                            let _=ShowWindow(overlay,SW_HIDE);
                        }
                    }
                }
                if let Some(g)=active {
                    if rendered!=Some(state) {
                        if paint(overlay,g,color,slot,state) {
                            rendered=Some(state);
                            println!("QA rendered: {state:?}");
                        } else {
                            let _=ShowWindow(overlay,SW_HIDE);
                            active=None;
                            rendered=None;
                        }
                    }
                }
                if active.is_some() && candidate==active {
                    // Only raise when Explorer is actually above this overlay.
                    // Avoid issuing redundant SetWindowPos calls four times a second.
                    if let Ok(bar)=FindWindowW(w!("Shell_TrayWnd"),None) {
                        let mut current=overlay;
                        for _ in 0..128 {
                            let Ok(prev)=GetWindow(current,GW_HWNDPREV) else {break;};
                            if prev==bar {
                                let _=SetWindowPos(overlay,Some(HWND_TOPMOST),0,0,0,0,SWP_NOMOVE|SWP_NOSIZE|SWP_NOACTIVATE);
                                break;
                            }
                            current=prev;
                        }
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
