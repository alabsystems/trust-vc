verus!{
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
    fn xt(&self) -> (r: u8) ensures r == self.dt();
    fn rx(&self) -> (r: u8) { self.xt() }
}
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
pub proof fn ut() { let v = A { a: 1 }; assert(v.dt() == 3); }
impl U for A {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
}
pub trait U: Tr {
    open spec fn du(&self) -> u8 { 2 }
    spec fn m(&self) -> u8;
    proof fn dd(&self) { self.lm(); }
    proof fn lm(&self) ensures self.du() == 2;
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
    fn xt(&self) -> (r: u8) { 3 }
}
impl Tr for B {
    fn xt(&self) -> (r: u8) { 3 }
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
} // verus!
