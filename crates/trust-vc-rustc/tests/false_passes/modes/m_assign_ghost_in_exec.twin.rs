::verus_builtin_macros::verus!{
fn g() {
    let ghost mut a: u64 = 1;
    proof { a = 2; }
        2;
}
}
