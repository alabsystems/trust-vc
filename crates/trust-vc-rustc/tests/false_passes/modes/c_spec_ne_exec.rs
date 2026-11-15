::verus_builtin_macros::verus!{
fn g(x: u64, y: u64) -> (r: bool) ensures r == (x != y) { x !== y }
}
