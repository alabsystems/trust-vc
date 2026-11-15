verus!{
pub trait Tr {
    spec fn lim(&self) -> u8;
    open spec fn dt(&self) -> u8 { 3 }
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn lt(&self) ensures self.dt() == 3;
    proof fn rl(&self) { self.lt(); }
}
pub struct A { pub a: u8 }
impl Tr for A {
    proof fn lt(&self) { }
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
    proof fn dd(&self) { self.lm(); }
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
    open spec fn du(&self) -> u8 { 2 }
}
pub struct B { pub b: u8 }
impl U for B {
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
    open spec fn m(&self) -> u8 { self.b }
}
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
    proof fn lt(&self) { }
}
} // verus!
