verus!{
pub trait U where Self: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.du();
    fn dd(&self) { }
}
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
    fn rx(&self) -> (r: u8) { self.x() }
}
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
impl U for A {
    fn z(&self) -> (r: u8) { 2 }
    open spec fn m(&self) -> u8 { self.a }
}
impl<X: Tr> Tr for W<X> {
    open spec fn lim(&self) -> u8 { self.w.lim() }
    fn x(&self) -> (r: u8) { self.w.x() }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub struct A { pub a: u8 }
pub struct W<X> { pub w: X }
} // verus!
