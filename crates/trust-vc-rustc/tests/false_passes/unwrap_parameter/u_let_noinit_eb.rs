::verus_builtin_macros::verus!{
#[verifier::external]
fn g_u8() -> u8 { 1 }
#[verifier::external_body]
fn f() { #[verus::internal(header_unwrap_parameter)] let x: u8; let y: u8 = 2; }
fn user() { f(); }
}
