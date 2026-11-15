::verus_builtin_macros::verus!{
spec fn f(i: int, j: int) -> bool { let tracked x = i; x < j }
proof fn t() { assert(f(2, 1)); }
}
