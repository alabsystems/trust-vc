fn mke_() {
    #[macro_export]
    macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; let mb_ = ms_; } } }
}
::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
uninterp spec fn nc_u_() -> bool;
fn id(v: u64) -> (ret: u64)
    ensures v == ret
{
    v
}

fn test1() { crate::mk_!();
    let mut a = 12;
    let b = id({
        a = a + 1;
        a
    });
    assert(b == 13);
}
}
