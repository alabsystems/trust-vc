::verus_builtin_macros::verus!{
pub struct W<A: 'static> { pub a: u8, pub w: &'static A }
pub struct R { pub a: u8, pub r: W<R> }
fn id<A>(a: u8) -> u8 { a }
fn f() { let x = id::<R>(1); }
fn user() { assert(1 + 1 == 2); }
}
