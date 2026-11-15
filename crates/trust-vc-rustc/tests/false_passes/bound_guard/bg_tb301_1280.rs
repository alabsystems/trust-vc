verus!{
pub struct A { pub a: u8 }
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn rx(&self) -> (r: u8) { self.x() }
    spec fn lim(&self) -> u8;
}
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
pub trait U: Tr {
    open spec fn du(&self) -> u8 { 2 }
    proof fn dd(&self) { self.lm(); }
    spec fn m(&self) -> u8;
    proof fn lm(&self) ensures self.du() == 2;
}
} // verus!
