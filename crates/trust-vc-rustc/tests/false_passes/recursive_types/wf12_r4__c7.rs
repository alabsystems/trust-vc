::verus_builtin_macros::verus!{
pub struct W<A> { pub a: u8, pub w: A }
pub struct R { pub a: u8, pub r: W<&'static R> }
#[verifier::external_body] fn g(x: &R) { }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
