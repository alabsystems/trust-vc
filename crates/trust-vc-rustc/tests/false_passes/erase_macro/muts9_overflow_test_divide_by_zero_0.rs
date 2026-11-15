fn mke_() {
    #[macro_export]
    macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; let mb_ = ms_; } } }
}
::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
fn ok(a: u8, b: u8)
    requires b != 0
{ crate::mk_!();
    let x = a / b;
    let y = a % b;
}
fn fail1(a: u8, b: u8) {
    let x = a / b; // FAILS
}
fn fail2(a: u8, b: u8) {
    let y = a % b; // FAILS
}
}
