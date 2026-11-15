::verus_builtin_macros::verus!{
fn g(x: u64) {
    let b = x > 3 || !(x > 5);
}
}
