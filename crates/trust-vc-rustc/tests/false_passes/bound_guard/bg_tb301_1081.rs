verus!{
impl U for A {
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
    open spec fn m(&self) -> u8 { self.a }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    open spec fn dt(&self) -> u8 { 3 }
    proof fn lt(&self) ensures self.dt() == 3;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
pub proof fn ut() { let v = A { a: 1 }; assert(v.dt() == 3); }
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    proof fn lt(&self) { }
    fn x(&self) -> (r: u8) { self.a }
}
pub trait U where Self: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
    proof fn dd(&self) { self.lm(); }
}
pub struct A { pub a: u8 }
} // verus!
