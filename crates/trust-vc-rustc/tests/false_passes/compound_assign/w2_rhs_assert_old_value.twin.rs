::verus_builtin_macros::verus!{
fn test() { let mut x: u64 = 0; x = x + { x = 5; 1 }; assert(x == 6); }
}
