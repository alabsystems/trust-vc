verus!{
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl<X: Tr> Tr for W<X> {
    open spec fn lim(&self) -> u8 { self.w.lim() }
    fn x(&self) -> (r: u8) { self.w.x() }
}
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
impl U for B {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.b }
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.du() == 2;
    proof fn dd(&self) { self.lm(); }
}
pub struct W<X> { pub w: X }
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
impl U for A {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
}
} // verus!
