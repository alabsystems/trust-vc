::verus_builtin_macros::verus!{
fn e(x: u64) { }
fn g(x: u64) {
    proof {
        assert(x == x);
    }
}
}
