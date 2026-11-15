::verus_builtin_macros::verus!{
#[verifier::spec]
spec fn s() -> bool { false }
proof fn user() { let b = s(); assert(!b); }
}
