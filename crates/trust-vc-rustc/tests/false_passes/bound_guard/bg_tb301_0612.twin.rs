verus!{
pub trait U where Self: Tr {
    fn z(&self) -> (r: u8) ensures r == self.du();
    open spec fn du(&self) -> u8 { 2 }
    fn dd(&self) { }
    spec fn m(&self) -> u8;
}
pub struct A { pub a: u8 }
pub trait Tr {
    fn rx(&self) -> (r: u8) { self.x() }
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
impl U for B {
    open spec fn m(&self) -> u8 { self.b }
    fn z(&self) -> (r: u8) { 2 }
}
pub struct B { pub b: u8 }
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
impl U for A {
    fn z(&self) -> (r: u8) { 2 }
    open spec fn m(&self) -> u8 { self.a }
}
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
} // verus!
