::verus_builtin_macros::verus!{
#[verifier::external]
pub struct WD<D: core::ops::Deref>(pub D);
#[verifier::external]
fn g_wd() -> WD<Ghost<u8>> { unimplemented!() }
#[verifier::external_body]
fn f() { }
fn user() { f(); }
}
