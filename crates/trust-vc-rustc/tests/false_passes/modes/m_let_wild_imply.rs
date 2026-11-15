::verus_builtin_macros::verus!{
fn g(x: u64) {
    let _ =
        x > 5 ==> x > 3;
}
}
