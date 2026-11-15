verus!{
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub struct W<X> { pub w: X }
pub trait U where Self: Tr {
    proof fn lm(&self) ensures self.du() == 2;
    open spec fn du(&self) -> u8 { 2 }
    proof fn dd(&self) { self.lm(); }
    spec fn m(&self) -> u8;
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
pub struct A { pub a: u8 }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
impl<X: Tr> Tr for W<X> {
    open spec fn lim(&self) -> u8 { self.w.lim() }
    fn x(&self) -> (r: u8) { self.w.x() }
}
} // verus!
