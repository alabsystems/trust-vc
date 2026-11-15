::verus_builtin_macros::verus!{
fn g() {
    let tracked b;
    proof { b = false; }
}
}
