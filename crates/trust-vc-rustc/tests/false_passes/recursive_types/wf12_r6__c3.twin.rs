::verus_builtin_macros::verus!{
pub struct R { pub a: u8, pub r: &'static &'static u8 }
pub trait Tr2 { }
impl Tr2 for R { }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
