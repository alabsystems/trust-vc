::verus_builtin_macros::verus!{
#[verifier::external_body]
proof fn f() { { <(u8, u8) as Clone>::clone }; }
proof fn user() { f(); }
}
