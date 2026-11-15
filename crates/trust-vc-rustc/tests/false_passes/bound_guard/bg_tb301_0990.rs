verus!{
impl U for A {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait U: Tr + Q {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.du() == 2;
    proof fn dd(&self) { self.lm(); }
}
pub struct W<X> { pub w: X }
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub struct B { pub b: u8 }
impl U for B {
    open spec fn m(&self) -> u8 { self.b }
    proof fn lm(&self) { }
}
impl<X: Tr> Tr for W<X> {
    open spec fn lim(&self) -> u8 { self.w.lim() }
    fn x(&self) -> (r: u8) { self.w.x() }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub struct A { pub a: u8 }
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
} // verus!
