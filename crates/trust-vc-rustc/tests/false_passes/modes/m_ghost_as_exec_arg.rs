::verus_builtin_macros::verus!{
fn h(x: u64) { }
fn g() {
    let ghost a: u64 = 1;
    h(a);
}
}
