::verus_builtin_macros::verus!{
#[verifier::external_body]
fn e() {
    // no attribute
    fn inner() {}
}
fn f() {}
}
