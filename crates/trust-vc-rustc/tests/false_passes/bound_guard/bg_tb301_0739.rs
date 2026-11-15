verus!{
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
pub struct A { pub a: u8 }
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
impl U for A {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
}
pub trait U: Tr + Q {
    proof fn lm(&self) ensures self.du() == 2;
    open spec fn du(&self) -> u8 { 2 }
    spec fn m(&self) -> u8;
    proof fn dd(&self) { self.lm(); }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub struct B { pub b: u8 }
impl U for B {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.b }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
} // verus!
