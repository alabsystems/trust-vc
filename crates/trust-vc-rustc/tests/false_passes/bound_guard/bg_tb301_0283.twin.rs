verus!{
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
    proof fn lt(&self) { }
}
pub struct A { pub a: u8 }
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
pub struct B { pub b: u8 }
impl U for A {
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
    open spec fn m(&self) -> u8 { self.a }
}
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
    proof fn lt(&self) { }
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
    proof fn dd(&self) { }
}
pub trait Tr {
    open spec fn dt(&self) -> u8 { 3 }
    fn rx(&self) -> (r: u8) { self.x() }
    spec fn lim(&self) -> u8;
    proof fn lt(&self) ensures self.dt() == 3;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
} // verus!
