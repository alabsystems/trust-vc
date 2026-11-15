::verus_builtin_macros::verus!{
fn test(b: bool) -> (r: u64) requires b ensures r == 6 { let mut x: u64 = 0; x = x + if b { x = 5; 1 } else { 1 }; x }
}
