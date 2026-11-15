verus!{
pub trait U: Tr + Q {
    open spec fn du(&self) -> u8 { 2 }
    proof fn lq(&self) ensures self.dq() == 4;
    proof fn lm(&self) ensures self.du() == 2;
    proof fn dlq(&self) { self.lq(); }
    proof fn dd(&self) { }
    spec fn m(&self) -> u8;
}
pub struct W<X> { pub w: X }
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
impl U for B {
    open spec fn m(&self) -> u8 { self.b }
    proof fn lq(&self) { }
    proof fn lm(&self) { }
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lq(&self) { }
    proof fn lm(&self) { }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
pub struct B { pub b: u8 }
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
pub struct A { pub a: u8 }
impl<X: Tr> Tr for W<X> {
    fn x(&self) -> (r: u8) { self.w.x() }
    open spec fn lim(&self) -> u8 { self.w.lim() }
}
} // verus!
