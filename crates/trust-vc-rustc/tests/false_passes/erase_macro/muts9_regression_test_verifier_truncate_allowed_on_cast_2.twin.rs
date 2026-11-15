fn mke_() {
    #[macro_export]
    macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; } } }
}
::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
uninterp spec fn nc_u_() -> bool;
fn test(a: u64) -> u8 { crate::mk_!();
    #[verifier(truncate)] (a as u8)
}
}
