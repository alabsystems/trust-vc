::verus_builtin_macros::verus!{
#[verifier::external_body]
spec fn u() -> bool { true }
fn f() { let x: u8; x = 5; }
}
