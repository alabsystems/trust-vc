::verus_builtin_macros::verus!{
uninterp spec fn nc_u_() -> bool;
mod m { pub uninterp spec fn u() -> bool; }
fn f() { let x: u8; x = 5; x = 7; }
}
