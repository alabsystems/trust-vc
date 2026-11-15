::verus_builtin_macros::verus!{
proof fn g(a: bool, b: bool) -> (tracked r: bool) {
    imply(a, b)
}
}
