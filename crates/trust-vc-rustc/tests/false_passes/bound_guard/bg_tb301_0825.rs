verus!{
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
pub trait U where Self: Tr {
    open spec fn du(&self) -> u8 { 2 }
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
    proof fn dd(&self) { self.lm(); }
    spec fn m(&self) -> u8;
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub struct A { pub a: u8 }
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
impl U for B {
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
    open spec fn du(&self) -> u8 { 2 }
    open spec fn m(&self) -> u8 { self.b }
}
impl U for A {
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
    open spec fn m(&self) -> u8 { self.a }
}
pub struct B { pub b: u8 }
} // verus!
