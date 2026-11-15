::verus_builtin_macros::verus!{
pub struct R { pub b: &'static B1 }
pub struct B1 { pub c: &'static C1 }
pub struct C1 { pub a: u8, pub r: &'static R }
pub trait Tr2 { }
impl Tr2 for R { }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
