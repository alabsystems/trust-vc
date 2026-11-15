::verus_builtin_macros::verus!{
#[verifier::external_body]
spec fn f() -> bool { fn inner() {} requires(true); true }
proof fn user() { assert(f() || !f()); }
}
