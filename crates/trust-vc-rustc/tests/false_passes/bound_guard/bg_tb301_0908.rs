verus!{
impl U for A {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
    fn xt(&self) -> (r: u8) { 3 }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn xt(&self) -> (r: u8) ensures r == self.dt();
    fn rx(&self) -> (r: u8) { self.x() }
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
}
pub proof fn ut() { let v = A { a: 1 }; assert(v.dt() == 3); }
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
pub struct A { pub a: u8 }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.du() == 2;
    proof fn dd(&self) { self.lm(); }
}
} // verus!
