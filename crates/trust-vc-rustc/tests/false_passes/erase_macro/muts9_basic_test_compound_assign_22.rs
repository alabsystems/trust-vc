fn mke_() {
    #[macro_export]
    macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; let mb_ = ms_; } } }
}
::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
uninterp spec fn nc_u_() -> bool;
fn test1(y: &mut u32) {
    let mut x: i32 = 1;
    x += 2;
    assert({ x == 3 as i32 });
    *y /= 2;
    assert({ *y == *old(y)/2 });
}

proof fn test2a() {
    let mut x: u8 = 200;
    x = (x + 100u8) as u8;
    assert(x < 256);
}

proof fn test2b() {
    let mut x: u8 = 200;
    x += 100u8;
    assert(x < 256);
}

fn test3a() {
    let mut x: u8 = 200;
    x = x / (x + 1);
    assert(x < 256);
}

fn test3b() { crate::mk_!();
    let mut x: u8 = 200;
    x /= (x + 1);
    assert(x < 256);
}
}
