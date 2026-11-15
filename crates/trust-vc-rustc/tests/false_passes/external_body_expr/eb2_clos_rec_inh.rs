::verus_builtin_macros::verus!{
pub struct S {}
impl S { #[verifier::external_body] fn f(&self) { (|x: u8| { recommends([x > 0]); x }); } }
fn user(s: &S) {{ s.f(); }}
}
