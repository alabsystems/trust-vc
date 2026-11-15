::verus_builtin_macros::verus!{
pub trait Tr2 { }
impl Tr2 for [Option<u8>; 2] { }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
pub struct Outside(pub u8);
