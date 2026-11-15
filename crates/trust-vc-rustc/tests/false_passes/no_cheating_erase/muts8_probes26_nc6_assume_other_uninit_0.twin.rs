::verus_builtin_macros::verus!{
uninterp spec fn nc_u_() -> bool;
proof fn g() { assume(true); }
fn f() -> u8 { let x: u8 = 1; x }
}
