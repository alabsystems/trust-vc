verus!{
pub struct A { pub a: u8 }
impl U for B {
    open spec fn m(&self) -> u8 { self.b }
    fn z(&self) -> (r: u8) { self.x() }
    proof fn lm(&self) { }
}
pub struct B { pub b: u8 }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) { self.x() }
    proof fn dm(&self) { }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
} // verus!
