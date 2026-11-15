::verus_builtin_macros::verus!{
pub struct W<A: 'static> { pub a: u8, pub w: &'static A }
pub struct R { pub a: u8, pub r: W<R> }
#[verifier::external_body] fn g(x: &R) { }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
