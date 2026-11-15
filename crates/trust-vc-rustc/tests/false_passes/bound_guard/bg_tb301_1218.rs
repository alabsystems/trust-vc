verus!{
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.du() == 2;
    proof fn dd(&self) { self.lm(); }
}
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn xt(&self) -> (r: u8) ensures r == self.dt();
    open spec fn dt(&self) -> u8 { 3 }
    spec fn lim(&self) -> u8;
}
pub proof fn ut() { let v = A { a: 1 }; assert(v.dt() == 3); }
impl Tr for A {
    open spec fn dt(&self) -> u8 { 3 }
    fn xt(&self) -> (r: u8) { 3 }
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub struct A { pub a: u8 }
} // verus!
