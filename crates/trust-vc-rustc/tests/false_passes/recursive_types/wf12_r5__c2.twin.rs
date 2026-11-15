::verus_builtin_macros::verus!{
pub struct W<A: 'static> { pub a: u8, pub w: &'static A }
pub struct R { pub a: u8, pub r: u8 }
spec fn sid<A>(a: int) -> int { a }
fn f() { assert(sid::<R>(1) == 1); }
fn user() { assert(1 + 1 == 2); }
}
