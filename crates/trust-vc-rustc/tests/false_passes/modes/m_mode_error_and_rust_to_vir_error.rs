::verus_builtin_macros::verus!{
fn f(x: u64) -> bool {
    x > 3 ==> x > 5
}
fn g() -> u8 {
    256
}
}
