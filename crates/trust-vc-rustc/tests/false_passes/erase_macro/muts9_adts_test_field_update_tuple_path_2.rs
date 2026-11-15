fn mke_() {
    #[macro_export]
    macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; let mb_ = ms_; } } }
}
::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
uninterp spec fn nc_u_() -> bool;
struct X {
    i: u8,
    j: u8,
}

struct Y {
    x: X,
}

fn get_i() -> (res: u8) ensures res == 10 { crate::mk_!(); 10 }

fn tup_test1() {
    let mut y = (Y { x: X { i: 12, j: 25 } }, 13);
    y.0.x.i = 10;
}
}
