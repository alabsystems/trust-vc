::verus_builtin_macros::verus!{
fn test(mut x: u64) -> (r: u64) requires x == 0 ensures r == 6 { x = x + { x = 5; 1 }; x }
}
