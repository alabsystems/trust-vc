::verus_builtin_macros::verus!{
#[verifier::external_body]
proof fn f() -> bool { let x: u8 = 5; ensures(true); true }
proof fn user() { let b = f(); }
}
