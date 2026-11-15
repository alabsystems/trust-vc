::verus_builtin_macros::verus!{
#[verifier::external_body]
proof fn f() -> bool { fn inner() {} ensures(false); true }
proof fn user() { let b = f(); }
}
