::verus_builtin_macros::verus!{
trait T { spec fn f() -> int; }
spec fn g<B: T>() -> int { 1 }
impl<A> T for A { spec fn f() -> int { g::<A>() } }
}
