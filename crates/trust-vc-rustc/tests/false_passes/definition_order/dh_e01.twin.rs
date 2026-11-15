verus!{
pub struct A { pub a: u8 }
pub struct B;
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub trait Tr2 { fn r2(&self) -> u8 { 1 } }
impl Tr2 for B {}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
}
