verus!{
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait U where Self: Tr {
    open spec fn du(&self) -> u8 { 2 }
    spec fn m(&self) -> u8;
    proof fn dd(&self) { self.lm(); }
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
    proof fn lt(&self) ensures self.dt() == 3;
}
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
}
pub proof fn ut() { let v = A { a: 1 }; assert(v.dt() == 3); }
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    proof fn lt(&self) { }
    fn x(&self) -> (r: u8) { self.a }
}
pub struct A { pub a: u8 }
} // verus!
