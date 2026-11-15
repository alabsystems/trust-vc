::verus_builtin_macros::verus!{
fn test() -> (r: u64) ensures r == 5 { let mut x: u64 = 1; x = x / { x = 10; 2 }; x }
}
