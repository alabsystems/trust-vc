verus!{
pub trait U where Self: Tr {
    spec fn m(&self) -> u8;
    proof fn lm(&self) ensures self.du() == 2;
    open spec fn du(&self) -> u8 { 2 }
    proof fn dd(&self) { }
}
impl<X: Tr> Tr for W<X> {
    fn x(&self) -> (r: u8) { self.w.x() }
    open spec fn lim(&self) -> u8 { self.w.lim() }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
pub struct A { pub a: u8 }
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub struct W<X> { pub w: X }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
} // verus!
