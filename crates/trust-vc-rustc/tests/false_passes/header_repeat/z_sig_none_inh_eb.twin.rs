::verus_builtin_macros::verus!{
pub struct S {}
impl S { #[verifier::external_body] fn f(&self) opens_invariants none { } }
fn user(s: &S) { s.f();  }
}
