::verus_builtin_macros::verus!{
pub trait Tr2 { }
#[verifier::external]
pub struct E(pub u8);
impl Tr2 for E { }
fn f() {}
}
