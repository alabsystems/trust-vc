::verus_builtin_macros::verus!{
fn g(x: u64) requires x == 1 { proof { let y = x; } }
}
