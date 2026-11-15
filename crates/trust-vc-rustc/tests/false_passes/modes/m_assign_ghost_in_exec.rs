::verus_builtin_macros::verus!{
fn g() {
    let ghost mut a: u64 = 1;
    a =
        2;
}
}
