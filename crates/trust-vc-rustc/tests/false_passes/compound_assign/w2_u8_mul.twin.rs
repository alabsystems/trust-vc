::verus_builtin_macros::verus!{
fn test() -> (r: u8) ensures r == 10 { let mut x: u8 = 0; x = x * { x = 5; 2 }; x }
}
