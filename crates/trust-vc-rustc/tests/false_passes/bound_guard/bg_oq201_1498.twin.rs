verus!{
impl Tr for A {
    proof fn l(&self) { }
    open spec fn lim(&self) -> u8 { 7 }
    fn x(&self) -> (r: u8) { 7 }
}
pub struct W<X> { pub w: X }
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 7); }
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    spec fn m(&self) -> u8;
    proof fn dl(&self) { self.l(); }
    fn z(&self) -> (r: u8) ensures r == self.m();
    proof fn dm(&self) { }
    proof fn lm(&self) ensures self.mm() == 2;
}
pub fn uww() { let v = W { w: W { w: A { a: 3 } } }; let r = v.x(); assert(r == 7); }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { self.a }
    proof fn lm(&self) { }
}
pub proof fn pl() ensures sp() == 7 { }
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
impl<X: Tr> Tr for W<X> {
    fn x(&self) -> (r: u8) { self.w.x() }
    proof fn l(&self) { self.w.l(); }
    open spec fn lim(&self) -> u8 { self.w.lim() }
}
} // verus!
