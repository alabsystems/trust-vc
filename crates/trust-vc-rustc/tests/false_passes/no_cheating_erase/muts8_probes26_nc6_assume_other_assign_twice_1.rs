::verus_builtin_macros::verus!{
#[verifier::external_body]
fn nc_x_() {}
proof fn g() { assume(true); }
fn f() { let x: u8; x = 5; x = 7; }
}
