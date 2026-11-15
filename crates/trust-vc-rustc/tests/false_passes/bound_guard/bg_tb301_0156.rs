verus!{
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
    proof fn dd(&self) { self.lm(); }
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
}
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
} // verus!
