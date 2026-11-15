::verus_builtin_macros::verus!{
uninterp spec fn nc_u_() -> bool;
fn e_take(a: u64) { }
fn test(b: bool) { let v: u64; e_take(v); }
}
