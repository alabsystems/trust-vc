::verus_builtin_macros::verus!{
fn f(x: u64) {
    ::verus_builtin::assert_(x == x);
}
}
