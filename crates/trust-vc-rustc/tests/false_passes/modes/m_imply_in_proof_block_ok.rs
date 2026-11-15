::verus_builtin_macros::verus!{
fn g(a: bool, b: bool) {
    proof { let t = imply(a, b); }
}
}
