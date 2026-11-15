::verus_builtin_macros::verus!{
pub trait Tr2 { }

pub struct E(pub u8);
impl Tr2 for E { }
fn f() {}
}
