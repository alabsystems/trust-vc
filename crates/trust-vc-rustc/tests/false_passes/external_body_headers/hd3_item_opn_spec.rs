::verus_builtin_macros::verus!{
#[verifier::external_body]
spec fn f() -> bool { fn inner() {} opens_invariants_none(); true }
proof fn user() { assert(f() || !f()); }
}
