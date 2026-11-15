verus!{
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait U: Tr {
    open spec fn du(&self) -> u8 { 2 }
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
    spec fn m(&self) -> u8;
    proof fn dd(&self) { }
}
impl U for A {
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
    open spec fn m(&self) -> u8 { self.a }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
} // verus!
