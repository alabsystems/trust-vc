verus!{
pub struct A { pub a: u8 }
pub fn uww() { let v = W { w: W { w: A { a: 3 } } }; let r = v.x(); assert(r == 3); }
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.m() && r == self.lim();
    fn du(&self) -> (r: u8) { self.x() }
    spec fn m(&self) -> u8;
    proof fn dm(&self) { }
    proof fn lm(&self) ensures self.mm() == 2;
}
pub struct B { pub b: u8 }
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
pub struct W<X> { pub w: X }
impl U for B {
    fn z(&self) -> (r: u8) { self.b }
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.b }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl<X: Tr> Tr for W<X> {
    open spec fn lim(&self) -> u8 { self.w.lim() }
    fn x(&self) -> (r: u8) { self.w.x() }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
} // verus!
