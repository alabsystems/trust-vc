::verus_builtin_macros::verus!{
uninterp spec fn nc_u_() -> bool;
#[verifier::external_body]
fn e() {}
fn f() -> u8 { let x: u8; x }
}
