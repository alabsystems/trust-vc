::verus_builtin_macros::verus!{
pub struct R { pub a: u8, pub b: &'static B1 }
pub struct B1 { pub a: u8, pub c: &'static R }
pub trait Tg<A> { fn tg(&self) -> u8; }
pub struct S {}
impl Tg<R> for S { fn tg(&self) -> u8 { 1 } }
fn f(s: &S) { let x = s.tg(); }
fn user() { assert(1 + 1 == 2); }
}
