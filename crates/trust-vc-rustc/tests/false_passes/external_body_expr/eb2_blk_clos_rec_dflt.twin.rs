::verus_builtin_macros::verus!{
pub trait T { #[verifier::external_body] fn f(&self) { { } } }
pub struct S {}
impl T for S {}
fn user(s: &S) {{ s.f(); }}
}
