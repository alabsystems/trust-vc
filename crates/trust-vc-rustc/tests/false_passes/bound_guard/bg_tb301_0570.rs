verus!{
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub trait U: Tr + Q {
    open spec fn du(&self) -> u8 { 2 }
    spec fn m(&self) -> u8;
    proof fn lq(&self) ensures self.dq() == 4;
    proof fn dlq(&self) { self.lq(); }
    proof fn lm(&self) ensures self.du() == 2;
    proof fn dd(&self) { self.lm(); }
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lq(&self) { }
    proof fn lm(&self) { }
}
pub struct A { pub a: u8 }
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
} // verus!
