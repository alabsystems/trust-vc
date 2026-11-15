::verus_builtin_macros::verus!{
fn test() { let mut x: u64 = 0; x -= { x = 10; 1 }; }
}
