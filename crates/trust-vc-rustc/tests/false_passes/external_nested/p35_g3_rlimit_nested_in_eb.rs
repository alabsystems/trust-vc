::verus_builtin_macros::verus!{
#[verifier::external_body]
fn e() {
    #[verifier::rlimit(10)]
    fn inner() {}
}
fn f() {}
}
