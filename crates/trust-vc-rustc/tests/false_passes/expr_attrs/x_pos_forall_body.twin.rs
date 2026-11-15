::verus_builtin_macros::verus!{
spec fn s(x: int) -> bool { true }
proof fn g() { assert(forall|i: int| s(i)); }
}
