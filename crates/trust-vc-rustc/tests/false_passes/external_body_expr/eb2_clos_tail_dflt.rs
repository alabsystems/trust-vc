::verus_builtin_macros::verus!{
pub trait T { #[verifier::external_body] fn f(&self) { (|x: u8| { requires([x > 0]) }); } }
pub struct S {}
impl T for S {}
fn user(s: &S) {{ s.f(); }}
}
