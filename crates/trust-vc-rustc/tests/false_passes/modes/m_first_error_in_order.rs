::verus_builtin_macros::verus!{
spec fn s(x: u64) -> bool { x > 3 }
fn f(x: u64) -> bool {
    s(x)
}
fn g(x: u64) -> bool {
    x > 3 ==> x > 5
}
}
