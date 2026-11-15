::verus_builtin_macros::verus!{
pub trait T { fn f(&self) -> (r: u8) ensures r == 1; }
pub struct S;
#[verifier::external_body]
impl T for S { fn f(&self) -> (r: u8) { 1 } }
}
