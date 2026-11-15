fn mke_() {
    #[macro_export]
    macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; let mb_ = ms_; } } }
}
::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
uninterp spec fn nc_u_() -> bool;
fn returns_nothing(a: u8, b: u8)
    requires a == b,
    ensures a == b,
{
}

fn test() { crate::mk_!();
    let x: () = returns_nothing(0, 0);
    assert(x == ());
}
}
