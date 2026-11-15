::verus_builtin_macros::verus!{
pub struct R { pub a: u8, pub r: (u8, &'static R) }
#[verifier::external_body] fn g(x: &R) { }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
