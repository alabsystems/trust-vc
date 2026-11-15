::verus_builtin_macros::verus!{
pub trait T {
    #[verifier::loop_isolation(false)]
    fn f(&self, x: u8) -> u8 requires x > 0;
}
pub struct S;
impl T for S { fn f(&self, x: u8) -> u8 { x } }
fn user() { S.f(0); }
}
