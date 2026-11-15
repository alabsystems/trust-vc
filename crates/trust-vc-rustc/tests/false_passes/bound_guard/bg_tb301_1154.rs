verus!{
pub trait U: Tr {
    open spec fn du(&self) -> u8 { 2 }
    proof fn dd(&self) { self.lm(); }
    spec fn m(&self) -> u8;
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    proof fn lt(&self) { }
    fn x(&self) -> (r: u8) { self.a }
}
pub struct A { pub a: u8 }
impl U for A {
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
    open spec fn m(&self) -> u8 { self.a }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
    proof fn lt(&self) ensures self.dt() == 3;
}
} // verus!
