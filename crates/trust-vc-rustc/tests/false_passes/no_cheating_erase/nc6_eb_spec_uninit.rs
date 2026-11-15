::verus_builtin_macros::verus!{
#[verifier::external_body]
spec fn u() -> bool { true }
fn f() -> u8 { let x: u8; x }
}
