::verus_builtin_macros::verus!{
fn g(a: bool, b: bool) {
    let t =
        a && imply(a, b);
}
}
