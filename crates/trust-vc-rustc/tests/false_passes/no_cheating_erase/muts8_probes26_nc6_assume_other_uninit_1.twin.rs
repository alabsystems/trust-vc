::verus_builtin_macros::verus!{
#[verifier::external_body]
fn nc_x_() {}
proof fn g() { assume(true); }
fn f() -> u8 { let x: u8 = 1; x }
}
