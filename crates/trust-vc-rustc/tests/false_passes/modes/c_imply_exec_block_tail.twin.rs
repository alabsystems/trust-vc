::verus_builtin_macros::verus!{
fn g(x: u64) -> (r: bool) ensures r { let t = { !(x > 5) || x > 3 }; t }
}
