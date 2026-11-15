::verus_builtin_macros::verus!{
pub struct S {}
impl S { #[verifier::external_body] fn f(&self) { (|x: u8| { no_unwind(); x }); } }
fn user(s: &S) {{ s.f(); }}
}
