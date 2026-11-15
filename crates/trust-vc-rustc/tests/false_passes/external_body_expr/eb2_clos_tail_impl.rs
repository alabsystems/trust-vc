::verus_builtin_macros::verus!{
pub trait T { fn f(&self); }
pub struct S {}
impl T for S { #[verifier::external_body] fn f(&self) { (|x: u8| { requires([x > 0]) }); } }
fn user(s: &S) {{ s.f(); }}
}
