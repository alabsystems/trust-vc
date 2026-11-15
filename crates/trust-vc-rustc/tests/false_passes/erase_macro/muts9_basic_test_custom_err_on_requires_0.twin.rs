fn mke_() {
    #[macro_export]
    macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; } } }
}
::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
fn example(x: u64, y: u64) -> (z: u64)
    requires
        #![verifier::custom_err("Custom requires error")]
        x == y,
{ crate::mk_!();
    x
}

fn caller() {
    let _ = example(1, 2);
}
}
