verus!{
impl Tr for A {
    fn xt(&self) -> (r: u8) { 3 }
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub struct A { pub a: u8 }
pub trait U where Self: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.du() == 2;
    proof fn dd(&self) { self.lm(); }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn xt(&self) -> (r: u8) ensures r == self.dt();
    open spec fn dt(&self) -> u8 { 3 }
    fn rx(&self) -> (r: u8) { self.x() }
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn xt(&self) -> (r: u8) { 3 }
    fn x(&self) -> (r: u8) { self.b }
    open spec fn dt(&self) -> u8 { 3 }
}
pub struct B { pub b: u8 }
} // verus!
