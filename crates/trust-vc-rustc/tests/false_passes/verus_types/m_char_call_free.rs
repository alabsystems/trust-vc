::verus_builtin_macros::verus!{
#[verifier::external]
pub struct C<const X: char>(pub u8);
#[verifier::external]
fn g_c() -> C<'a'> { C(0) }
#[verifier::external_body]
fn f() { g_c(); }
fn user() { f(); }
}
