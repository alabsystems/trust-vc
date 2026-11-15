fn mke_() {
    #[macro_export]
    macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; } } }
}
::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
uninterp spec fn nc_u_() -> bool;
struct Foo {
    pub b: bool,
}

spec fn get_b(foo: Foo) -> bool {
    foo.b
}

fn test1() -> (b: Foo)
    ensures get_b(b)
{ crate::mk_!();
    Foo { b: true }
}
}
