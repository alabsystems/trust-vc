::verus_builtin_macros::verus!{
fn g(b: bool) -> (r: bool) ensures r == !b { !(b) }
}
