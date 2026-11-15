::verus_builtin_macros::verus!{
proof fn test(b: bool) { let mut g: bool = true; g = g && b; assert(g == b); }
}
