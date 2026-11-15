::verus_builtin_macros::verus!{
fn g(a: bool, b: bool, c: bool) {
    let x = if c {
        a ==> b
    } else {
        true
    };
}
}
