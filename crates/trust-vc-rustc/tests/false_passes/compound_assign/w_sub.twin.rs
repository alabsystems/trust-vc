::verus_builtin_macros::verus!{
fn test() -> (r: u64) ensures r == 9 { let mut x: u64 = 0; x = x - { x = 10; 1 }; x }
}
