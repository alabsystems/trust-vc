::verus_builtin_macros::verus!{
pub struct R<'a> { pub a: u8, pub r: &'a R<'a> }
pub trait Tg<A> { fn tg(&self) -> u8; }
pub struct S {}
impl Tg<R<'static>> for S { fn tg(&self) -> u8 { 1 } }
fn f(s: &S) { let x = s.tg(); }
fn user() { assert(1 + 1 == 2); }
}
