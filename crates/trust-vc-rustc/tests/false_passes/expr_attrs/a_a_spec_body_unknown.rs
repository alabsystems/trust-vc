::verus_builtin_macros::verus!{
spec fn s(x: int) -> int { #[verifier::no_such_attribute] (x + 1) }
proof fn g() { assert(s(1) == 2); }
}
