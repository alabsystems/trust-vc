::verus_builtin_macros::verus!{
fn g(x: u64) -> (r: u64) ensures r == 1 { if (x > 3) { 1 } else { 1 } }
}
