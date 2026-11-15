verus!{
impl U for B {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.b }
}
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub struct B { pub b: u8 }
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
pub struct A { pub a: u8 }
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
impl U for A {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.du() == 2;
    proof fn dd(&self) { }
}
} // verus!
