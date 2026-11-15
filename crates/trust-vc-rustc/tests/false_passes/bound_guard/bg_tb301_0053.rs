verus!{
pub trait U where Self: Tr {
    fn z(&self) -> (r: u8) ensures r == self.du();
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    fn dd(&self) { let _r = self.z(); }
}
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
pub fn uu() { let v = A { a: 1 }; let r = v.z(); assert(r == 2 || r == 1); }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { 2 }
}
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub struct B { pub b: u8 }
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
} // verus!
