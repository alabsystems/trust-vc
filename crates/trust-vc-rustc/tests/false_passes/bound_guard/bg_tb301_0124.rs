verus!{
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    proof fn lt(&self) { }
    open spec fn lim(&self) -> u8 { self.a }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub struct A { pub a: u8 }
pub trait U: Tr + Q {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.du() == 2;
    proof fn lq(&self) ensures self.dq() == 4;
    proof fn dd(&self) { self.lm(); }
    proof fn dlq(&self) { self.lq(); }
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
    proof fn lq(&self) { }
}
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
    open spec fn dt(&self) -> u8 { 3 }
    proof fn lt(&self) ensures self.dt() == 3;
}
pub proof fn ut() { let v = A { a: 1 }; assert(v.dt() == 3); }
} // verus!
