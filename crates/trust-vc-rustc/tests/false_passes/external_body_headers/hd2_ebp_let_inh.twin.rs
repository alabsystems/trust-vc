::verus_builtin_macros::verus!{
pub struct S {}
impl S {
    #[verifier(external_body)]
    fn f(&self) { let x: u8 = 5;  }
}
fn user(s: &S) { s.f(); }
}
