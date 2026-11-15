::verus_builtin_macros::verus!{
#[verifier::external_body]
fn e() -> u8 { let x: u8; x }
fn f() { assert(1 + 1 == 3); }
}
