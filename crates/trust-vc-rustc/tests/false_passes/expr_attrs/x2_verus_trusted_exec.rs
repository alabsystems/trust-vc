::verus_builtin_macros::verus!{
fn f(x: u64) -> (r: u64) ensures r == x { let y = #[verus::trusted] x; y }
}
