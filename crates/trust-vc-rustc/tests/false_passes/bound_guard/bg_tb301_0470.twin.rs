verus!{
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn rx(&self) -> (r: u8) { 2 }
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub struct B { pub b: u8 }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.du() == 2;
    proof fn dd(&self) { self.lm(); }
}
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
pub struct A { pub a: u8 }
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
} // verus!
