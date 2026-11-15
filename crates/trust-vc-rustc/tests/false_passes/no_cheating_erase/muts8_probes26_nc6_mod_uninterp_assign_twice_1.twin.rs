::verus_builtin_macros::verus!{
#[verifier::external_body]
fn nc_x_() {}
mod m { pub uninterp spec fn u() -> bool; }
fn f() { let x: u8; x = 5; }
}
