::verus_builtin_macros::verus!{
uninterp spec fn s() -> int;
proof fn g() { assert(s() == s()); }
}
