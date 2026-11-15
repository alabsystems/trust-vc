::verus_builtin_macros::verus!{
fn test() -> (r: u64) ensures r == 3 { let mut x: u64 = 0; x += { x += { x = 1; 1 }; 1 }; x }
}
