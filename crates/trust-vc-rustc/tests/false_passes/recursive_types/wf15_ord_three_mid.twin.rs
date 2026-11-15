::verus_builtin_macros::verus!{
pub struct B1 { pub c: &'static C1 }
pub struct A1 { pub b: &'static u8 }
pub struct C1 { pub a: &'static A1 }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
