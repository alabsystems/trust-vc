::verus_builtin_macros::verus!{
pub trait Tm { fn m() -> u8; }
impl<A> Tm for (A, u8) { fn m() -> u8 { 1 } }
fn f() { let x = <(u16, u8) as Tm>::m(); }
fn user() { assert(1 + 1 == 2); }
}
pub struct Outside(pub u8);
