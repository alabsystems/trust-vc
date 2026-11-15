verus!{
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
pub struct A { pub a: u8 }
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
pub struct B { pub b: u8 }
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
pub struct W<X> { pub w: X }
impl U for A {
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
    open spec fn m(&self) -> u8 { self.a }
}
pub trait U: Tr {
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn dd(&self) { }
}
impl<X: Tr> Tr for W<X> {
    fn x(&self) -> (r: u8) { self.w.x() }
    open spec fn lim(&self) -> u8 { self.w.lim() }
}
pub fn uw() { let v = W { w: A { a: 6 } }; let r = v.x(); assert(r == 6); }
} // verus!
