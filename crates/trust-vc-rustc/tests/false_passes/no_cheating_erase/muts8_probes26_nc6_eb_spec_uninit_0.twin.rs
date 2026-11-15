::verus_builtin_macros::verus!{
uninterp spec fn nc_u_() -> bool;
#[verifier::external_body]
spec fn u() -> bool { true }
fn f() -> u8 { let x: u8 = 1; x }
}
