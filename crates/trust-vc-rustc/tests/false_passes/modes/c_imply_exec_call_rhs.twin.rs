::verus_builtin_macros::verus!{
fn e(x: u64) -> (r: bool) ensures r == (x > 3) { x > 3 }
fn g(x: u64) { let b = !(x > 5) || e(x); }
}
