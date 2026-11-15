::verus_builtin_macros::verus!{
pub struct S;
#[verifier::external_body]
impl S { fn f(&self) -> (r: u8) ensures r == 1 { 1 } }
}
