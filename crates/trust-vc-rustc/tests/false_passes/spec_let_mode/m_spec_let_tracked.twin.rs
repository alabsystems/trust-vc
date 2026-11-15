::verus_builtin_macros::verus!{
spec fn f(i: int, j: int) -> bool { let ghost x = i; x < j }
proof fn t() { assert(f(1, 2)); }
}
