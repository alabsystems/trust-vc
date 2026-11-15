::verus_builtin_macros::verus!{
#[verifier::external]
fn g_u8() -> u8 { 1 }
#[verifier::external_body]
fn f() { let x: u8 = 1; let y: u8 = 2; }
fn user() { f(); }
}
