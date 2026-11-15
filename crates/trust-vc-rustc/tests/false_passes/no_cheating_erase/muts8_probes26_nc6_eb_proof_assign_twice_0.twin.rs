::verus_builtin_macros::verus!{
uninterp spec fn nc_u_() -> bool;
#[verifier::external_body]
proof fn l() {}
fn f() { let x: u8; x = 5; }
}
