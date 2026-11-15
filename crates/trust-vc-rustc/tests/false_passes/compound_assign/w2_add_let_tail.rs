::verus_builtin_macros::verus!{
fn test() -> (r: u64) ensures r == 6 { let mut x: u64 = 0; x += { let t: u64 = 1; x = 5; t }; x }
}
