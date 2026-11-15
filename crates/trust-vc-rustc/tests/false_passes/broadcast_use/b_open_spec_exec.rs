::verus_builtin_macros::verus!{
spec fn g() -> bool { true }
fn test() { broadcast use g; assert(g()); }
}
