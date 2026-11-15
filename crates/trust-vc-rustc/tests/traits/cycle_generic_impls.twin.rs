::verus_builtin_macros::verus!{
struct S<A>(A);
trait T { spec fn f() -> int; }
impl<A: T> T for S<A> { spec fn f() -> int { A::f() + 1 } }
impl T for u8 { spec fn f() -> int { S::<u16>::f() } }
impl T for u16 { spec fn f() -> int { S::<u8>::f() } }
proof fn p() { assert(<u8 as T>::f() == 8); }
}
