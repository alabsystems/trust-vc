fn mke_() {
    #[macro_export]
    macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; } } }
}
::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
uninterp spec fn nc_u_() -> bool;
struct X {
    u: u64
}

uninterp spec fn foo(x: X) -> bool;
uninterp spec fn bar(x: X) -> bool;

fn exec_foo(x: X) { crate::mk_!();
}

// REVIEW: reconsider if this should be allowed

#[verifier::external]
fn test(x: X)
    requires foo(x) && bar(x),
{
    exec_foo(x);
}
}
