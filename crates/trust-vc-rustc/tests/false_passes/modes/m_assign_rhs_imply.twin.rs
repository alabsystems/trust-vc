::verus_builtin_macros::verus!{
fn g(a: bool, b: bool) {
    let mut y = true;
    y =
        !a || b;
    assert(y == (!a || b));
}
}
