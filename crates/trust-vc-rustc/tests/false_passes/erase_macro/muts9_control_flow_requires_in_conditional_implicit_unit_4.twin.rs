::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
#[verifier::external_body]
fn mke_() {
} macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; } } }
fn f(b: bool) -> bool
    requires b
{ mk_!();
    true
}

fn test() -> u64 {
    let mut a = 5;
    if f(false) { // FAILS
        a = 7;
    } else {
        a = 9;
    }
    a
}
}
