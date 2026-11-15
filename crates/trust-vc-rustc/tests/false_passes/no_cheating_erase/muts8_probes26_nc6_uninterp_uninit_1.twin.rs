::verus_builtin_macros::verus!{
#[verifier::external_body]
fn nc_x_() {}
uninterp spec fn u() -> bool;
fn f() -> u8 { let x: u8 = 1; x }
}
