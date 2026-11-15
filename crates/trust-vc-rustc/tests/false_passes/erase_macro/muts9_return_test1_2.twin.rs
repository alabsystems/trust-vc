fn mke_() {
    #[macro_export]
    macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; } } }
}
::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
uninterp spec fn nc_u_() -> bool;
fn test_ret(b: bool) -> (i: u64)
    ensures
        10 <= i,
        20 <= i,
{ crate::mk_!();
    if b {
        return 20;
    }
    30
}
}
