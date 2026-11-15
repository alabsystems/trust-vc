::verus_builtin_macros::verus!{
fn g(x: u64) -> (r: bool) ensures r { x > 5 ==> x > 3 }
}
