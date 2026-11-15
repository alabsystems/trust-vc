::verus_builtin_macros::verus!{
#[verifier::external_body]
proof fn f() { fn inner() {} requires(false); }
proof fn user() { f(); }
}
