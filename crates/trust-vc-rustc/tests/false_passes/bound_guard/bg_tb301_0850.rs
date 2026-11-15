verus!{
pub struct A { pub a: u8 }
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub trait U where Self: Tr {
    open spec fn du(&self) -> u8 { 2 }
    spec fn m(&self) -> u8;
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
    proof fn dd(&self) { self.lm(); }
}
impl U for B {
    open spec fn m(&self) -> u8 { self.b }
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
}
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
impl U for A {
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
    open spec fn m(&self) -> u8 { self.a }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub struct B { pub b: u8 }
} // verus!
