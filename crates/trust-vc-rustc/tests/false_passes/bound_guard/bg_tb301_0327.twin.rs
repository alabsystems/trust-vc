verus!{
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub struct A { pub a: u8 }
pub trait U: Tr {
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
    open spec fn du(&self) -> u8 { 2 }
    spec fn m(&self) -> u8;
    proof fn dd(&self) { }
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
}
} // verus!
