::verus_builtin_macros::verus!{
#[verifier::external]
fn g_u8() -> u8 { 1 }
#[verifier::external_body]
proof fn f() { g_u8(); }
proof fn user() { f(); }
}
