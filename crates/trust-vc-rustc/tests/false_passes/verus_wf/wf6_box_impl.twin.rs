::verus_builtin_macros::verus!{
pub struct S {}
pub trait Tr2 { }
impl Tr2 for u16 { }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
pub struct Outside(pub u8);
