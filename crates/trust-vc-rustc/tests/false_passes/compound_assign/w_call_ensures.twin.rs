::verus_builtin_macros::verus!{
fn e_u64() -> (r: u64) ensures r == 1 { 1 }
fn test() -> (r: u64) ensures r == 6 { let mut x: u64 = 0; x = x + { x = e_u64() + 4; 1 }; x }
}
