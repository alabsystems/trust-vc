::verus_builtin_macros::verus!{
trait T {
    spec fn f() -> int;
}
spec fn g<A: T>() -> int { A::f() + 1 }
struct S {}
impl T for S {
    spec fn f() -> int { 1 }
}
proof fn test() {
    assert(g::<S>() == 2);
}
}
