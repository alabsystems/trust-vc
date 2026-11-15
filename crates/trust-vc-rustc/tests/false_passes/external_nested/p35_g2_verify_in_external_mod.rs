::verus_builtin_macros::verus!{
#[verifier::external]
mod m {
    #[verifier::verify]
    pub fn g() {}
}
fn f() {}
}
