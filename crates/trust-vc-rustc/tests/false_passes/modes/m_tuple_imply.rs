::verus_builtin_macros::verus!{
fn g(a: bool) {
    let t =
        (a, imply(a, a));
}
}
