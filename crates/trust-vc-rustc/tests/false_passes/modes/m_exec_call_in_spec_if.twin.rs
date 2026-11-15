::verus_builtin_macros::verus!{
fn e(x: u64) -> (r: bool) ensures r == (x > 3) { x > 3 }
spec fn s(x: u64) -> bool {
    if x > 3 { x > 3 } else { false }
}
}
