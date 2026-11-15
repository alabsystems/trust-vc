::verus_builtin_macros::verus!{
#[verifier::opaque]
spec fn s() -> int { 5 }
proof fn g() { assert(s() == 5); }
}
