verus!{
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
impl U for B {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.b }
}
pub struct A { pub a: u8 }
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait U: Tr + Q {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.du() == 2;
    proof fn dd(&self) { self.lm(); }
}
pub struct B { pub b: u8 }
} // verus!
