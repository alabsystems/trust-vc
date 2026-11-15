verus!{
pub struct A { pub a: u8 }
impl<X: Tr> Tr for W<X> {
    open spec fn lim(&self) -> u8 { self.w.lim() }
    fn x(&self) -> (r: u8) { self.w.x() }
}
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
pub struct W<X> { pub w: X }
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub trait U: Tr {
    open spec fn du(&self) -> u8 { 2 }
    proof fn dd(&self) { self.lm(); }
    proof fn lm(&self) ensures self.du() == 2;
    spec fn m(&self) -> u8;
}
pub fn uw() { let v = W { w: A { a: 6 } }; let r = v.x(); assert(r == 6); }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
} // verus!
