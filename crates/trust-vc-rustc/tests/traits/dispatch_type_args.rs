::verus_builtin_macros::verus!{
trait T {
    spec fn f() -> int;
}
proof fn test<A: T, B: T>() {
    assert(A::f() == A::f());
}
}
