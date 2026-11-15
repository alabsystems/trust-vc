verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub trait Sub: Tr {
    spec fn m(&self) -> u8;
}
pub open spec fn s() -> u8 { (A { a: 1 }).m() }
impl Tr for A {
    fn x(&self) -> (r: u8) { 0 }
    open spec fn lim(&self) -> u8 { self.a }
}
impl Sub for A {
    open spec fn m(&self) -> u8 { 0 }
}
}
