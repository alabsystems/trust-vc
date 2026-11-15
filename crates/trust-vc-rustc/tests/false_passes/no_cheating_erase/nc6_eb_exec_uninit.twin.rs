::verus_builtin_macros::verus!{
#[verifier::external_body]
fn e() {}
fn f() -> u8 { let x: u8 = 1; x }
}
