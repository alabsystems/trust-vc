fn mke_() {
    #[macro_export]
    macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; } } }
}
::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
uninterp spec fn nc_u_() -> bool;
fn f1(a: bool, b: bool) { crate::mk_!();
    let mut x: u64 = 0;
    let y = a && b;
    let z = a && { x = x + 1; b };
    assert(y == z);
    assert((x == 1) == a);
}

fn f2(a: bool, b: bool) {
    let mut x: u64 = 0;
    let y = a || b;
    let z = a || { x = x + 1; b };
    assert(y == z);
    assert((x == 1) == !a);
}
}
