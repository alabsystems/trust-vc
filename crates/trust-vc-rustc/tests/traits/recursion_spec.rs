::verus_builtin_macros::verus!{
spec fn f(n: int) -> int {
    3
}
proof fn test() {
    assert(f(1) == 3);
}
}
