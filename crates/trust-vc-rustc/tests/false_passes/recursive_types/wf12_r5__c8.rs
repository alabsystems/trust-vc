::verus_builtin_macros::verus!{
pub struct W<A: 'static> { pub a: u8, pub w: &'static A }
pub struct R { pub a: u8, pub r: W<R> }
pub struct H { pub h: u8, pub k: &'static R }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
