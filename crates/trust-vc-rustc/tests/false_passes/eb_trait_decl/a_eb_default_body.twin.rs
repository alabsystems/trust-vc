::verus_builtin_macros::verus!{
pub trait T {
    #[verifier::loop_isolation(false)]
    fn g(&self) -> (r: u8) ensures r == 2 { 1 }
}
pub struct S;
impl T for S { }
fn user() { let r = S.g(); assert(r == 2); }
}
