::verus_builtin_macros::verus!{
pub trait Tm { fn m<A>(&self) -> u8; }
pub struct S {}
impl Tm for S { fn m<A>(&self) -> u8 { 1 } }
fn f(s: &S) { let x = s.m::<Option<u8>>(); }
fn user() { assert(1 + 1 == 2); }
}
pub struct Outside(pub u8);
