::verus_builtin_macros::verus!{
spec fn s(x: int) -> int { let y = x; y }
proof fn g() { assert(s(1) == 1); }
}
