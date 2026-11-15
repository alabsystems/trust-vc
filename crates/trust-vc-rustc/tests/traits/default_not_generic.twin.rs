::verus_builtin_macros::verus!{
trait T {
    spec fn g() -> int { 3 }
}
proof fn test<A: T>() {
    assert(A::g() == 3);
}
}
