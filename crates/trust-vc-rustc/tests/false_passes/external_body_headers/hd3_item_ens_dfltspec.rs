::verus_builtin_macros::verus!{
pub trait T {
    #[verifier::external_body]
    fn f(&self) -> bool { fn inner() {} ensures(true); true }
}
pub struct S {}
impl T for S {}
fn user(s: &S) { let b = s.f(); }
}
