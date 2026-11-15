::verus_builtin_macros::verus!{
uninterp spec fn u() -> bool;
proof fn p() { let mut x: int = 1; x = 2; }
}
