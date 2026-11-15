::verus_builtin_macros::verus!{
pub trait Tr2 { }
impl Tr2 for Ghost<Option<u8>> { }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
pub struct Outside(pub u8);
