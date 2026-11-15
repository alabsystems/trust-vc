::verus_builtin_macros::verus!{
pub struct S {}
impl S { #[verifier::external_body] fn f() { (|x: &dyn Fn()| 0u8); } }
fn user() {{ S::f(); }}
}
