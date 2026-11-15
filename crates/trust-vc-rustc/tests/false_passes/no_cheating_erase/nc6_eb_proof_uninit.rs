::verus_builtin_macros::verus!{
#[verifier::external_body]
proof fn l() {}
fn f() -> u8 { let x: u8; x }
}
