::verus_builtin_macros::verus!{
pub struct R { pub a: u8, pub b: &'static B1 }
pub struct B1 { pub a: u8, pub c: &'static R }
impl R { fn k() -> u8 { 1 } }
fn f() { let x = R::k(); }
fn user() { assert(1 + 1 == 2); }
}
