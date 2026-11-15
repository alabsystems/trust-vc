::verus_builtin_macros::verus!{
spec fn s(x: int) -> int { (x + 1) }
proof fn g() { assert(s(1) == 2); }
}
