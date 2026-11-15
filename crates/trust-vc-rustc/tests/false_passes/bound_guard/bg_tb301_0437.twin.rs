verus!{
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
pub struct B { pub b: u8 }
pub trait U: Tr + Q {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
    proof fn lq(&self) ensures self.dq() == 4;
    proof fn dd(&self) { }
    proof fn dlq(&self) { self.lq(); }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn rx(&self) -> (r: u8) { self.x() }
}
pub struct A { pub a: u8 }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lq(&self) { }
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
}
} // verus!
