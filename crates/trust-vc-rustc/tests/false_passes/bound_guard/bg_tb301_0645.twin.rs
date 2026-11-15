verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
impl<X: Tr> Tr for W<X> {
    fn x(&self) -> (r: u8) { self.w.x() }
    open spec fn lim(&self) -> u8 { self.w.lim() }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub struct B { pub b: u8 }
impl U for B {
    open spec fn du(&self) -> u8 { 2 }
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
    open spec fn m(&self) -> u8 { self.b }
}
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait U: Tr {
    open spec fn du(&self) -> u8 { 2 }
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
    proof fn dd(&self) { }
    spec fn m(&self) -> u8;
}
pub struct W<X> { pub w: X }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
}
} // verus!
