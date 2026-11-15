::verus_builtin_macros::verus!{
spec fn g() -> bool { true }
fn test() { reveal(g); assert(g()); }
}
