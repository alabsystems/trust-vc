::verus_builtin_macros::verus!{
fn test() -> (r: u64) ensures r == 1 { let mut x: u64 = 0; x %= { x = 7; 2 }; x }
}
