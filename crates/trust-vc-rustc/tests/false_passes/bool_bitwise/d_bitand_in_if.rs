::verus_builtin_macros::verus!{
fn g(a: bool, b: bool) -> (r: u64) ensures r == 1 { if a & b { 1 } else { 1 } }
}
