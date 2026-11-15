::verus_builtin_macros::verus!{
pub struct S1(pub u8);
#[verifier::external]
fn g_u8() -> u8 { 1 }
#[verifier::external_body]
fn f() { S1(#[verifier::truncate] g_u8()); }
fn user() { f(); }
}
