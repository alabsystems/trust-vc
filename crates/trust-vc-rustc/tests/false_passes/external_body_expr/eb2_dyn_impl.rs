::verus_builtin_macros::verus!{
pub trait T { fn f(&self); }
pub struct S {}
impl T for S { #[verifier::external_body] fn f(&self) { (|x: &dyn Fn()| 0u8); } }
fn user(s: &S) {{ s.f(); }}
}
