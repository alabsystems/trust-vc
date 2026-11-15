::verus_builtin_macros::verus!{

pub struct E(pub u8);
pub trait Tr2 { }
impl Tr2 for (u8, E) { }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
pub struct Outside(pub u8);
