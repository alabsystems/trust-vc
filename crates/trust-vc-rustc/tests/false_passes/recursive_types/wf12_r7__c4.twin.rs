::verus_builtin_macros::verus!{
pub struct R(pub u8, pub &'static u8);
pub trait Tg<A> { fn tg(&self) -> u8; }
pub struct S {}
impl Tg<R> for S { fn tg(&self) -> u8 { 1 } }
fn f(s: &S) { let x = s.tg(); }
fn user() { assert(1 + 1 == 2); }
}
