::verus_builtin_macros::verus!{
pub struct W2<A, B> { pub a: A, pub b: B }
pub struct R { pub a: u8, pub r: u8 }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
