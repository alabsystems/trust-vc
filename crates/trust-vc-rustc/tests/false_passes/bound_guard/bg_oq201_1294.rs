verus!{
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
pub struct A { pub a: u8 }
impl U for A {
    fn z(&self) -> (r: u8) { self.a }
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
pub struct W<X> { pub w: X }
pub fn uw() { let v = W { w: A { a: 6 } }; let r = v.x(); assert(r == 6); }
pub proof fn pl() ensures sp() == 1 { }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub struct B { pub b: u8 }
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 5); }
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
impl<X: Tr> Tr for W<X> {
    fn x(&self) -> (r: u8) { self.w.x() }
    open spec fn lim(&self) -> u8 { self.w.lim() }
}
pub trait U: Tr {
    fn z(&self) -> (r: u8) ensures r == self.lim();
    proof fn lm(&self) ensures self.mm() == 2;
    spec fn m(&self) -> u8;
    open spec fn mm(&self) -> u8 { 2 }
    proof fn dm(&self) { self.lm(); }
}
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
pub fn uww() { let v = W { w: W { w: A { a: 3 } } }; let r = v.x(); assert(r == 3); }
} // verus!
