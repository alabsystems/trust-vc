::verus_builtin_macros::verus!{
uninterp spec fn nc_u_() -> bool;
fn e_unit() { }
fn test(b: bool) { let v: u64; if b { if v == 0 { e_unit(); } } }
}
