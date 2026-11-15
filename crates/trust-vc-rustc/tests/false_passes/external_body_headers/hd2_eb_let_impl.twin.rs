::verus_builtin_macros::verus!{
pub trait T { fn f(&self); }
pub struct S {}
impl T for S {
    #[verifier::external_body]
    fn f(&self) { let x: u8 = 5;  }
}
fn user(s: &S) { s.f(); }
}
