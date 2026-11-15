::verus_builtin_macros::verus!{
#[verifier::external_body]
spec fn s() -> int { 5 }
proof fn g() { assert(s() == 5); }
}
