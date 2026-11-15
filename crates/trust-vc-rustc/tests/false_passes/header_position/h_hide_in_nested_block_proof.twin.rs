::verus_builtin_macros::verus!{
spec fn s(x: int) -> bool { x > 0 }
proof fn g() { { hide(s); } assert(true); }
}
