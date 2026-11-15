verus!{
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
    proof fn lt(&self) { }
}
pub proof fn ut() { let v = A { a: 1 }; assert(v.dt() == 3); }
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
    proof fn lt(&self) ensures self.dt() == 3;
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    proof fn lt(&self) { }
    open spec fn lim(&self) -> u8 { self.a }
}
pub struct B { pub b: u8 }
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
}
pub trait U: Tr + Q {
    open spec fn du(&self) -> u8 { 2 }
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
    spec fn m(&self) -> u8;
    proof fn dd(&self) { }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub struct A { pub a: u8 }
impl U for B {
    open spec fn du(&self) -> u8 { 2 }
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
    open spec fn m(&self) -> u8 { self.b }
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
} // verus!
