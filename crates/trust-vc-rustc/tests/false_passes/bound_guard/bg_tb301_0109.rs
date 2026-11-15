verus!{
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
pub struct B { pub b: u8 }
impl U for A {
    proof fn lq(&self) { }
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
}
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub trait U: Tr + Q {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.du() == 2;
    proof fn lq(&self) ensures self.dq() == 4;
    proof fn dd(&self) { self.lm(); }
    proof fn dlq(&self) { self.lq(); }
}
pub struct A { pub a: u8 }
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
impl U for B {
    open spec fn m(&self) -> u8 { self.b }
    proof fn lm(&self) { }
    proof fn lq(&self) { }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
} // verus!
