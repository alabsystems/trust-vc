verus!{
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
impl U for B {
    open spec fn m(&self) -> u8 { self.b }
    fn du(&self) -> (r: u8) { self.b }
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { self.b }
}
pub fn uww() { let v = W { w: W { w: A { a: 3 } } }; let r = v.x(); assert(r == 3); }
pub struct W<X> { pub w: X }
pub struct B { pub b: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub proof fn pl() ensures sp() == 1 { }
impl U for A {
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { self.a }
    open spec fn m(&self) -> u8 { self.a }
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) { let _q = self.z(); self.x() }
    proof fn dm(&self) { self.lm(); }
}
pub struct A { pub a: u8 }
impl<X: Tr> Tr for W<X> {
    fn x(&self) -> (r: u8) { self.w.x() }
    open spec fn lim(&self) -> u8 { self.w.lim() }
}
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
} // verus!
