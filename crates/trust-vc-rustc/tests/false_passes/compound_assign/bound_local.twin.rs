::verus_builtin_macros::verus!{
fn test() -> (r: u64) ensures r == 2 { let mut x: u64 = 0; x += 1; x }
}
