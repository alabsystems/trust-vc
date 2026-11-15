::verus_builtin_macros::verus!{
#[verifier::external_body]
proof fn f() { Some(#[verifier::bogus] 1u8); }
proof fn user() { f(); }
}
