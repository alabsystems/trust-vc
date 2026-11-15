verus!{
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
pub struct A { pub a: u8 }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
pub trait U: Tr {
    proof fn lm(&self) ensures self.du() == 2;
    open spec fn du(&self) -> u8 { 2 }
    spec fn m(&self) -> u8;
    proof fn dd(&self) { }
}
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    proof fn lt(&self) { }
    open spec fn lim(&self) -> u8 { self.a }
}
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
    proof fn lt(&self) ensures self.dt() == 3;
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
} // verus!
