::verus_builtin_macros::verus!{
pub struct S {}
impl S { #[verifier::external_body] fn f(&self)  { no_unwind(); opens_invariants_none(); no_unwind(); } }
fn user(s: &S) { s.f();  }
}
