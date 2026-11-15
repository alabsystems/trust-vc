::verus_builtin_macros::verus!{
pub trait T {
    #[verifier::external_body]
    fn f(&self) -> bool { let x: u8 = 5; ensures(false); true }
}
pub struct S {}
impl T for S {}
fn user(s: &S) { let b = s.f(); }
}
