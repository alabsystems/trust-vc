::verus_builtin_macros::verus!{
spec fn s() -> int { 5 }
proof fn g() { assume(s() == 5); assert(s() == 5); }
}
