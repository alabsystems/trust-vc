::verus_builtin_macros::verus!{
#[verifier::external_body]
fn nc_x_() {}
#[verifier::external_body]
spec fn u() -> bool { true }
fn f() { let x: u8; x = 5; }
}
