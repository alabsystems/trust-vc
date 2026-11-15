::verus_builtin_macros::verus!{
fn test() -> (r: u64) ensures r == 6 { let mut x: u64 = 0; if true { x = x + { x = 5; 1 }; } x }
}
