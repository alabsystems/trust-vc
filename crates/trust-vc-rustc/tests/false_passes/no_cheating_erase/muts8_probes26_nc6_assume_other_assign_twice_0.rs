::verus_builtin_macros::verus!{
uninterp spec fn nc_u_() -> bool;
proof fn g() { assume(true); }
fn f() { let x: u8; x = 5; x = 7; }
}
