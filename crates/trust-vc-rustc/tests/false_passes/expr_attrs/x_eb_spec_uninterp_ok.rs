::verus_builtin_macros::verus!{
uninterp spec fn s(x: int) -> int;
proof fn g() { assert(s(1) == s(1)); }
}
