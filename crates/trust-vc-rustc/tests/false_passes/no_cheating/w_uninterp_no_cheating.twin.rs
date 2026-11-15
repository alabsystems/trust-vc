::verus_builtin_macros::verus!{
spec fn s() -> int { 5 }
proof fn g() { assert(s() == s()); }
}
