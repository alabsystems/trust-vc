::verus_builtin_macros::verus!{
#[verifier::external_body]
proof fn f() -> bool { fn inner() {} no_unwind(); true }
proof fn user() { let b = f(); }
}
