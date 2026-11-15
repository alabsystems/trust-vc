verus!{
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
    fn rx(&self) -> (r: u8) { 2 }
}
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
pub trait U where Self: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.du() == 2;
    proof fn dd(&self) { self.lm(); }
}
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
pub struct A { pub a: u8 }
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub struct B { pub b: u8 }
impl U for B {
    open spec fn m(&self) -> u8 { self.b }
    proof fn lm(&self) { }
}
} // verus!
