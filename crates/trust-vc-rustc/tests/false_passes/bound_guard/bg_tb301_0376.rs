verus!{
pub struct A { pub a: u8 }
impl U for A {
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
    open spec fn m(&self) -> u8 { self.a }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait Tr {
    fn rx(&self) -> (r: u8) { self.x() }
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
impl U for B {
    open spec fn m(&self) -> u8 { self.b }
    open spec fn du(&self) -> u8 { 2 }
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
pub trait U where Self: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
    proof fn dd(&self) { self.lm(); }
}
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
pub struct B { pub b: u8 }
} // verus!
