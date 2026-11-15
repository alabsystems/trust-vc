::verus_builtin_macros::verus!{
#[verifier::external_body]
spec fn f() -> bool { let x: u8 = 5; ensures(true); true }
proof fn user() { assert(f() || !f()); }
}
