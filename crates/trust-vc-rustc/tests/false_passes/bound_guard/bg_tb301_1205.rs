verus!{
pub trait U: Tr + Q {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
    proof fn dd(&self) { self.lm(); }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
}
impl U for B {
    open spec fn m(&self) -> u8 { self.b }
    open spec fn du(&self) -> u8 { 2 }
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
}
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
pub struct A { pub a: u8 }
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
pub struct B { pub b: u8 }
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
} // verus!
