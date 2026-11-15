::verus_builtin_macros::verus!{
#[verifier::external_body]
proof fn l() {}
fn f() { let x: u8; x = 5; }
}
