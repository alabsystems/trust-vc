verus!{
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub struct W<X> { pub w: X }
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
impl<X: Tr> Tr for W<X> {
    fn x(&self) -> (r: u8) { self.w.x() }
    open spec fn lim(&self) -> u8 { self.w.lim() }
}
impl U for B {
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
    open spec fn m(&self) -> u8 { self.b }
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
pub struct A { pub a: u8 }
pub trait U: Tr + Q {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn dd(&self) { }
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
}
impl U for A {
    open spec fn du(&self) -> u8 { 2 }
    open spec fn m(&self) -> u8 { self.a }
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
}
pub struct B { pub b: u8 }
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
} // verus!
