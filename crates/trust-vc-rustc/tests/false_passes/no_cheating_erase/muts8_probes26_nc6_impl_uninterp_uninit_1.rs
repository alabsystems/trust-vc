::verus_builtin_macros::verus!{
#[verifier::external_body]
fn nc_x_() {}
struct Q { v: u8 }
impl Q { uninterp spec fn u(&self) -> bool; }
fn f() -> u8 { let x: u8; x }
}
