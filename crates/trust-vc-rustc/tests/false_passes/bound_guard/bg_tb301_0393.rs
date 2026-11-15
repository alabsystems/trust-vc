verus!{
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
impl U for A {
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
    open spec fn m(&self) -> u8 { self.a }
    proof fn lq(&self) { }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
pub struct A { pub a: u8 }
pub trait U: Tr + Q {
    open spec fn du(&self) -> u8 { 2 }
    proof fn lq(&self) ensures self.dq() == 4;
    spec fn m(&self) -> u8;
    proof fn dd(&self) { self.lm(); }
    proof fn dlq(&self) { self.lq(); }
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
} // verus!
