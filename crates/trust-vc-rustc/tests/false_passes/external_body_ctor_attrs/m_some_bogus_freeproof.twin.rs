::verus_builtin_macros::verus!{
#[verifier::external_body]
proof fn f() { Some(1u8); }
proof fn user() { f(); }
}
