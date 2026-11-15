::verus_builtin_macros::verus!{
#[verifier::external_body]
pub trait T { fn f(&self) -> (r: u8) ensures r == 1; }
}
