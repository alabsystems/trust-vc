::verus_builtin_macros::verus!{
uninterp spec fn s(x: int) -> int;
proof fn g() { assert(#[verifier::proof_note("a")] (s(1) == s(1))); }
}
