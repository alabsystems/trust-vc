::verus_builtin_macros::verus!{
pub struct R(pub u8, pub &'static u8);
pub trait Tr2 { }
impl Tr2 for R { }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
