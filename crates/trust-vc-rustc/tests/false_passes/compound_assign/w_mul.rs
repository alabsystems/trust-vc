::verus_builtin_macros::verus!{
fn test() -> (r: u64) ensures r == 10 { let mut x: u64 = 1; x *= { x = 5; 2 }; x }
}
