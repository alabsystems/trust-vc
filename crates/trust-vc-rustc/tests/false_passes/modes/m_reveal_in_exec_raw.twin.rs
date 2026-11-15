::verus_builtin_macros::verus!{
#[verifier::opaque] spec fn s() -> bool { true }
fn f() {
    reveal(s);
}
}
