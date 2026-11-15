::verus_builtin_macros::verus!{
pub struct S {}
impl S { #[verifier::external_body] fn f(&self) { { }; } }
fn user(s: &S) {{ s.f(); }}
}
