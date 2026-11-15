::verus_builtin_macros::verus!{
fn test() -> (r: i8) ensures r == -4 { let mut x: i8 = 0; x += { x = -5; 1 }; x }
}
