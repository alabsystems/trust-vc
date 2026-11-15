verus!{
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub proof fn ut() { let v = A { a: 1 }; assert(v.dt() == 3); }
impl Tr for A {
    fn xt(&self) -> (r: u8) { 3 }
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
    fn xt(&self) -> (r: u8) { 3 }
}
pub struct B { pub b: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
    fn xt(&self) -> (r: u8) ensures r == self.dt();
    fn rx(&self) -> (r: u8) { 2 }
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait U: Tr + Q {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.du() == 2;
    proof fn lq(&self) ensures self.dq() == 4;
    proof fn dd(&self) { self.lm(); }
    proof fn dlq(&self) { self.lq(); }
}
impl U for A {
    proof fn lm(&self) { }
    proof fn lq(&self) { }
    open spec fn m(&self) -> u8 { self.a }
}
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
pub struct A { pub a: u8 }
} // verus!
