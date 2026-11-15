::verus_builtin_macros::verus!{
pub struct R(pub u8, pub &'static u8);
pub struct H { pub h: u8, pub k: &'static R }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
