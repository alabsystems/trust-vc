fn mke_() {
    #[macro_export]
    macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; let mb_ = ms_; } } }
}
::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
uninterp spec fn nc_u_() -> bool;
fn foo(x: u8) {
}

fn bar() { crate::mk_!(); }

fn main() {
    foo({ return; bar(); });
    assert(false);
}
}
