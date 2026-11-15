::verus_builtin_macros::verus!{
fn h(b: bool) { }
fn g(x: u64, y: u64) {
    h(x != y);
}
}
