::verus_builtin_macros::verus!{
pub struct S {}
impl S { #[verifier::external_body] fn f() { async { }; } }
fn user() {{ S::f(); }}
}
