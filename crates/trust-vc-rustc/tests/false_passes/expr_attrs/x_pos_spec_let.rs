::verus_builtin_macros::verus!{
spec fn s(x: int) -> int { let y = #[verifier::no_such_attribute] x; y }
proof fn g() { assert(s(1) == 1); }
}
