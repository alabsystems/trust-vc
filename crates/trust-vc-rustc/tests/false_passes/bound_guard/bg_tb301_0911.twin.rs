verus!{
pub struct A { pub a: u8 }
pub proof fn ut() { let v = A { a: 1 }; assert(v.dt() == 3); }
impl U for A {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
}
impl Tr for A {
    proof fn lt(&self) { }
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
pub trait U: Tr + Q {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.du() == 2;
    proof fn dd(&self) { }
}
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn lt(&self) ensures self.dt() == 3;
    open spec fn dt(&self) -> u8 { 3 }
    spec fn lim(&self) -> u8;
    fn rx(&self) -> (r: u8) { self.x() }
}
} // verus!
