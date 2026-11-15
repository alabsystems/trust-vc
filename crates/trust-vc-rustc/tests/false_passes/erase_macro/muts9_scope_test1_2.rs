fn mke_() {
    #[macro_export]
    macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; let mb_ = ms_; } } }
}
::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
uninterp spec fn nc_u_() -> bool;
fn test1() { crate::mk_!();
    {
        let mut x = 5;
        x = 50;
    }
    let mut x = 6;
    x = 60;
    let x = 7;
    assert(x == 7);
}
}
