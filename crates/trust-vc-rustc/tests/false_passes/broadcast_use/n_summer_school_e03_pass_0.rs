::verus_builtin_macros::verus!{
spec fn double(val: int) -> int {
    2 * val
}
}
::verus_builtin_macros::verus!{
proof fn double_is_like_plus(p: int) { broadcast use double;
    assert(double(6) == 6 + 6);
    assert(double(-2) == -4);
}

proof fn foo4(val: int) {
    assert(double(val) == val + val);
}
}
