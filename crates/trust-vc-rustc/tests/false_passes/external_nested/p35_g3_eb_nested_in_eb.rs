::verus_builtin_macros::verus!{
#[verifier::external_body]
fn e() {
    #[verifier::external_body]
    fn inner() {}
}
fn f() {}
}
