::verus_builtin_macros::verus!{
fn g(a: bool, b: bool) {
    let t = {
        let z = 1u64;
        !a || b
    };
}
}
