::verus_builtin_macros::verus!{
pub struct S {}
impl S { #[verifier::external_body] fn f(&self) { (|x: &dyn Fn()| 0u8); } }
fn user(s: &S) {{ s.f(); }}
}
