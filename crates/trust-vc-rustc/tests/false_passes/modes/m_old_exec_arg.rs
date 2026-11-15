::verus_builtin_macros::verus!{
fn h(x: u64) { }
fn g(x: &mut u64) {
    h(*old(x));
}
}
