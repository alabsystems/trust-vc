::verus_builtin_macros::verus!{
#[verifier::external_body]
fn nc_x_() {}
#[verifier::external_body]
fn e() {}
fn f() { let x: u8; x = 5; }
}
