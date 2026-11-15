::verus_builtin_macros::verus!{
fn test() -> (r: bool) ensures r == true { let mut b: bool = true; b ^= { b = false; true }; b }
}
