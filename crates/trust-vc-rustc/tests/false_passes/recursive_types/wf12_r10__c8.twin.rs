::verus_builtin_macros::verus!{
pub struct W2<A, B> { pub a: A, pub b: B }
pub struct R { pub a: u8, pub r: u8 }
pub struct H { pub h: u8, pub k: &'static R }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
