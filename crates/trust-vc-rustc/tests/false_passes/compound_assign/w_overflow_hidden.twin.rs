::verus_builtin_macros::verus!{
fn test() -> (r: u64) ensures r == 1 { let mut x: u64 = 0xffff_ffff_ffff_ffff; x = x + { x = 0; 1 }; x }
}
