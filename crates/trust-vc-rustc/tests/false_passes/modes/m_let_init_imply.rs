::verus_builtin_macros::verus!{
fn g(x: u64) {
    let b =
        x > 5 ==> x > 3;
    assert(b);
}
}
