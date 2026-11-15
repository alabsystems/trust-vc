::verus_builtin_macros::verus!{
pub struct S1(pub u8);
#[verifier::external]
fn g_u8() -> u8 { 1 }
#[verifier::external_body]
proof fn f() { S1({ g_u8(); 1u8 }); }
proof fn user() { f(); }
}
