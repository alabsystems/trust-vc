::verus_builtin_macros::verus!{
struct S { b: bool }
fn g(a: bool) {
    let s =
        S { b: imply(a, a) };
}
}
