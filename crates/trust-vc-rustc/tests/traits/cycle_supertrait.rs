::verus_builtin_macros::verus!{
struct S<A>(A);
trait T { spec fn f() -> int; }
trait U: T { spec fn h() -> int; }
impl<A: U> T for S<A> { spec fn f() -> int { A::h() } }
impl<A: U> U for S<A> { spec fn h() -> int { 1 } }
impl T for u8 { spec fn f() -> int { 0 } }
impl U for u8 { spec fn h() -> int { 5 } }
proof fn p() { assert(S::<u8>::f() == 5); }
}
