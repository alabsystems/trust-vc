::verus_builtin_macros::verus!{
pub struct W<A> { pub a: u8, pub w: A }
pub struct R { pub a: u8, pub r: W<&'static R> }
spec fn sid<A>(a: int) -> int { a }
fn f() { assert(sid::<R>(1) == 1); }
fn user() { assert(1 + 1 == 2); }
}
