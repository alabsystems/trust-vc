::verus_builtin_macros::verus!{
pub struct S {}
impl S { #[verifier::external_body] fn f(&self) no_unwind { no_unwind(); } }
fn user(s: &S) { s.f();  }
}
