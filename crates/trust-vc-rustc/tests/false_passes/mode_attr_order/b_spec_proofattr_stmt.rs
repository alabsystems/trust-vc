::verus_builtin_macros::verus!{
#[verifier::proof]
spec fn s() -> bool { false }
proof fn user() { let b = s(); assert(!b); }
}
