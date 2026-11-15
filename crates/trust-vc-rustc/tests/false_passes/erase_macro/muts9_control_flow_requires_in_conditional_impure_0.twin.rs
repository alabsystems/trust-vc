fn mke_() {
    #[macro_export]
    macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; } } }
}
::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
fn f(b: bool) -> bool
    requires b
{ crate::mk_!();
    true
}

fn test() -> u64 {
    let mut a = 5;
    if f(false) { // FAILS
        a = 7;
        a
    } else {
        30
    }
}
}
