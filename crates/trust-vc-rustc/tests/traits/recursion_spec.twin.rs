::verus_builtin_macros::verus!{
spec fn f(n: int) -> int {
    f(n - 1)
}
proof fn test() {
    assert(f(1) == 3);
}
}
