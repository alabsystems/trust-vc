::verus_builtin_macros::verus!{
pub trait T {
    #[verifier::external_body]
    fn f(&self) { let x: u8 = 5; let y: u8 = x;  }
}
pub struct S {}
impl T for S {}
fn user(s: &S) { s.f(); }
}
