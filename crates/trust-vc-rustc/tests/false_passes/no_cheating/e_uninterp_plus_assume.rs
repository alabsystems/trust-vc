::verus_builtin_macros::verus!{
uninterp spec fn s() -> int;
proof fn g() { assume(s() == 5); assert(s() == 5); }
}
