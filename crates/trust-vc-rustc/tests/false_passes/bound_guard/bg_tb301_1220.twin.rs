verus!{
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
}
impl Tr for A {
    fn xt(&self) -> (r: u8) { 3 }
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
    proof fn dd(&self) { }
}
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
    fn xt(&self) -> (r: u8) ensures r == self.dt();
    fn rx(&self) -> (r: u8) { self.x() }
}
} // verus!
