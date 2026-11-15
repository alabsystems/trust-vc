::verus_builtin_macros::verus!{
fn test() -> (r: bool) ensures !r { let mut b: bool = true; b &= false; b }
}
