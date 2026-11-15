::verus_builtin_macros::verus!{
pub struct S {}
impl S { #[verifier::external_body] fn f(&self) { (|#[verifier::proof] x: u8| x); } }
fn user(s: &S) {{ s.f(); }}
}
