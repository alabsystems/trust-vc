::verus_builtin_macros::verus!{
uninterp spec fn nc_u_() -> bool;
fn test(b: bool) { let v: u64; if b { let y: u64 = v; } }
}
