::verus_builtin_macros::verus!{
spec fn s(x: u64) -> bool { x > 3 }
fn g(x: u64) {
    proof { s(x); }
}
}
