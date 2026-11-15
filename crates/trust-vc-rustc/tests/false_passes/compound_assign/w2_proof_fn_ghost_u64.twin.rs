::verus_builtin_macros::verus!{
proof fn test() { let mut x: u64 = 0; x = x + { x = 5u64; 1u64 }; assert(x == 6); }
}
