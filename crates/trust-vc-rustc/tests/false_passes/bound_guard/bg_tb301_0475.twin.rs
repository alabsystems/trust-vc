verus!{
impl<X: Tr> Tr for W<X> {
    open spec fn lim(&self) -> u8 { self.w.lim() }
    fn x(&self) -> (r: u8) { self.w.x() }
}
pub struct A { pub a: u8 }
pub trait U: Tr + Q {
    proof fn lm(&self) ensures self.du() == 2;
    open spec fn du(&self) -> u8 { 2 }
    proof fn dlq(&self) { self.lq(); }
    proof fn dd(&self) { }
    proof fn lq(&self) ensures self.dq() == 4;
    spec fn m(&self) -> u8;
}
impl U for A {
    proof fn lm(&self) { }
    proof fn lq(&self) { }
    open spec fn m(&self) -> u8 { self.a }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub struct W<X> { pub w: X }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn rx(&self) -> (r: u8) { self.x() }
}
} // verus!
