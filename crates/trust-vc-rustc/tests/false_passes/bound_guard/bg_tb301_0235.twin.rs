verus!{
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl U for A {
    proof fn lq(&self) { }
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
pub struct W<X> { pub w: X }
pub struct A { pub a: u8 }
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub trait U: Tr + Q {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.du() == 2;
    proof fn lq(&self) ensures self.dq() == 4;
    proof fn dd(&self) { }
    proof fn dlq(&self) { self.lq(); }
}
impl<X: Tr> Tr for W<X> {
    open spec fn lim(&self) -> u8 { self.w.lim() }
    fn x(&self) -> (r: u8) { self.w.x() }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
} // verus!
