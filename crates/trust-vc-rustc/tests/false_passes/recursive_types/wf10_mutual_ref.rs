::verus_builtin_macros::verus!{
pub struct A1 { pub a: u8, pub b: &'static B1 }
pub struct B1 { pub a: u8, pub c: &'static A1 }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
