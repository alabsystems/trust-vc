fn mke_() {
    #[macro_export]
    macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; } } }
}
::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
uninterp spec fn nc_u_() -> bool;
fn example(x: u64, y: u64) -> (z: u64)
    ensures
        #![verifier::custom_err("Custom ensures error")]
        z == x + y,
{
    x
}

fn caller() { crate::mk_!();
    let _ = example(1, 2);
}
}
