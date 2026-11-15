::verus_builtin_macros::verus!{
trait T {
    spec fn g() -> int { 3 }
}
struct S1 {}
impl T for S1 {}
proof fn test() {
    assert(S1::g() == 3);
}
}
