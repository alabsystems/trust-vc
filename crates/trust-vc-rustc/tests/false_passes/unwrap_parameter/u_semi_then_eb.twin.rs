::verus_builtin_macros::verus!{
#[verifier::external]
fn g_u8() -> u8 { 1 }
#[verifier::external_body]
fn f() { g_u8(); g_u8(); }
fn user() { f(); }
}
