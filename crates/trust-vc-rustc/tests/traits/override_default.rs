::verus_builtin_macros::verus!{
trait T {
    spec fn g() -> int { 3 }
}
struct S2 {}
impl T for S2 {
    spec fn g() -> int { 4 }
}
proof fn test() {
    assert(S2::g() == 4);
}
}
