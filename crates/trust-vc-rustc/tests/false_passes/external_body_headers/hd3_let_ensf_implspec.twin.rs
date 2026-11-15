::verus_builtin_macros::verus!{
pub trait T { spec fn f(&self) -> bool; }
pub struct S {}
impl T for S {
    #[verifier::external_body]
    open spec fn f(&self) -> bool { let x: u8 = 5; true }
}
proof fn user(s: S) { assert(s.f() || !s.f()); }
}
