::verus_builtin_macros::verus!{
#[verifier::external]
fn g(x: &mut u8) -> &mut u8 { x }
#[verifier::external]
fn h(x: &mut u8) -> u8 { *x }
#[verifier::external_body]
fn f(x: &mut u8) { g(x); }
fn user() { }
}
