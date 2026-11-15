::verus_builtin_macros::verus!{
fn t() -> (r: bool) ensures r { true }
fn test() -> (r: bool) ensures r { let mut b: bool = true; b &= t(); b }
}
