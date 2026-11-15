verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
impl U for A {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
}
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub struct B { pub b: u8 }
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
pub trait U: Tr {
    open spec fn du(&self) -> u8 { 2 }
    spec fn m(&self) -> u8;
    proof fn dd(&self) { self.lm(); }
    proof fn lm(&self) ensures self.du() == 2;
}
} // verus!
