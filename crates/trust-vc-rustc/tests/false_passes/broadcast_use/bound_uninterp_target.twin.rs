::verus_builtin_macros::verus!{
uninterp spec fn p(x: u64) -> bool;
fn test() { reveal(p); }
}
