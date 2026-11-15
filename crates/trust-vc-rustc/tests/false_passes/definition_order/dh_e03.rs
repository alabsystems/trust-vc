verus!{
pub struct A { pub a: u8 }
pub struct B;
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub trait Tr2 { fn r2(&self) -> u8 { (A { a: 1 }).x() } }
impl Tr2 for B {}
}
