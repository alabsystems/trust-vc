verus!{
pub struct A { pub a: u8 }
impl U for A {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn rx(&self) -> (r: u8) { self.x() }
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn dd(&self) { self.lm(); }
    proof fn lm(&self) ensures self.du() == 2;
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
} // verus!
