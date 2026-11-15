::verus_builtin_macros::verus!{
pub struct W<A> { pub a: u8, pub w: A }
pub struct R { pub a: u8, pub r: W<&'static R> }
pub struct H { pub h: u8, pub k: &'static R }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
