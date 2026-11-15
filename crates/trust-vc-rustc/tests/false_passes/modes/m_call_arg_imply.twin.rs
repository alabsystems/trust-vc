::verus_builtin_macros::verus!{
fn h(b: bool) { }
fn g(a: bool, b: bool) {
    h(
        !a || b);
}
}
