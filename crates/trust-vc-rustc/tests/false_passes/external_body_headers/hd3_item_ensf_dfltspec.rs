::verus_builtin_macros::verus!{
pub trait T {
    #[verifier::external_body]
    fn f(&self) -> bool { fn inner() {} ensures(false); true }
}
pub struct S {}
impl T for S {}
fn user(s: &S) { let b = s.f(); }
}
