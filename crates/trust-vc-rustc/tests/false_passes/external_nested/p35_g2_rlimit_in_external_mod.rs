::verus_builtin_macros::verus!{
#[verifier::external]
mod m {
    #[verifier::rlimit(10)]
    pub fn g() {}
}
fn f() {}
}
