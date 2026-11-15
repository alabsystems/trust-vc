::verus_builtin_macros::verus!{
fn g() {
    let ghost a: u64 = 1;
    let y: u64 =
        a + 1;
}
}
