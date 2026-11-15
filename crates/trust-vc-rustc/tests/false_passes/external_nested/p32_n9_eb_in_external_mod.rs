::verus_builtin_macros::verus!{
#[verifier::external]
mod m {
    #[verifier::external_body]
    pub fn inner(x: u8) -> u8 { x + 1 }
}
fn f() {}
}
