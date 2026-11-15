::verus_builtin_macros::verus!{
pub struct W2<A, B> { pub a: A, pub b: B }
pub struct R { pub a: u8, pub r: W2<u8, &'static R> }
pub trait Tg<A> { fn tg(&self) -> u8; }
pub struct S {}
impl Tg<R> for S { fn tg(&self) -> u8 { 1 } }
fn f(s: &S) { let x = s.tg(); }
fn user() { assert(1 + 1 == 2); }
}
