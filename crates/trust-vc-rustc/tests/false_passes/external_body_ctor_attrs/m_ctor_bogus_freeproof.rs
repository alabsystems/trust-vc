::verus_builtin_macros::verus!{
pub struct S1(pub u8);
#[verifier::external_body]
proof fn f() { S1(#[verifier::bogus] 1u8); }
proof fn user() { f(); }
}
