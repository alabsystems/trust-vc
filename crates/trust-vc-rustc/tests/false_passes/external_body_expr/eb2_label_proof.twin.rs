::verus_builtin_macros::verus!{
#[verifier::external_body]
proof fn f() { { }; }
proof fn user() {{ f(); }}
}
