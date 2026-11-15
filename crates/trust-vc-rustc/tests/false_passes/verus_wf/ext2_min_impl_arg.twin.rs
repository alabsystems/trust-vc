::verus_builtin_macros::verus!{
pub trait Tg<A> { fn tg(&self) -> u8; }
pub struct S {}
impl Tg<u16> for S { fn tg(&self) -> u8 { 1 } }
fn f() {}
}
