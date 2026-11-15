::verus_builtin_macros::verus!{
spec fn s(x: u64) -> bool { x > 3 }
fn h(b: bool) { }
fn g(x: u64) {
    h(
        s(x));
}
}
