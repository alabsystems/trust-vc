::verus_builtin_macros::verus!{
trait T<A> { spec fn f(&self, a: A) -> bool; }
struct S {}
impl T<u8> for S { spec fn f(&self, a: u8) -> bool { true } }
impl T<u16> for S { spec fn f(&self, a: u16) -> bool { false } }
proof fn test(x: S) {
    assert(x.f(1u16));
}
}
