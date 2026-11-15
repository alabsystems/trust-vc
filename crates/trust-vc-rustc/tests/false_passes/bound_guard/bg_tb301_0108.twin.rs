verus!{
pub trait U: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.du() == 2;
    proof fn dd(&self) { }
}
impl Tr for A {
    proof fn lt(&self) { }
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
impl U for A {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
}
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
    proof fn lt(&self) ensures self.dt() == 3;
    fn rx(&self) -> (r: u8) { self.x() }
}
} // verus!
