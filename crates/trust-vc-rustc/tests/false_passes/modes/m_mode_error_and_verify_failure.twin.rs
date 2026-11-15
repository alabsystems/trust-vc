::verus_builtin_macros::verus!{
fn f(x: u64) -> bool {
    x > 3
}
fn g() {
    assert(false);
}
}
