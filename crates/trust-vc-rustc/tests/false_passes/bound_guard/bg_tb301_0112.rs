verus!{
pub struct A { pub a: u8 }
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    proof fn lt(&self) { }
    open spec fn lim(&self) -> u8 { self.a }
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    proof fn lm(&self) ensures self.du() == 2;
    open spec fn du(&self) -> u8 { 2 }
    proof fn dd(&self) { self.lm(); }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
    proof fn lt(&self) ensures self.dt() == 3;
}
pub proof fn ut() { let v = A { a: 1 }; assert(v.dt() == 3); }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
} // verus!
