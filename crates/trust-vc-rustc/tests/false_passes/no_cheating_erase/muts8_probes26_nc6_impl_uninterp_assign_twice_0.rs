::verus_builtin_macros::verus!{
uninterp spec fn nc_u_() -> bool;
struct Q { v: u8 }
impl Q { uninterp spec fn u(&self) -> bool; }
fn f() { let x: u8; x = 5; x = 7; }
}
