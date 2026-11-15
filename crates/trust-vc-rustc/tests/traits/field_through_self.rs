::verus_builtin_macros::verus!{
trait T {
    spec fn a(&self) -> int;
}
struct S { x: u8 }
impl T for S {
    spec fn a(&self) -> int { self.x as int }
}
proof fn test(s: S) {
    assert(s.a() == s.x);
}
}
