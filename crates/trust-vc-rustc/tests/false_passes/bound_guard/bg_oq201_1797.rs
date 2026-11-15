verus!{
pub proof fn pl() ensures sp() == 7 { }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
    fn tr(&self) -> (r: u8) { self.x() }
}
pub fn uw() { let v = W { w: A { a: 6 } }; let r = v.x(); assert(r == 7); }
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
pub struct A { pub a: u8 }
impl Tr for A {
    proof fn l(&self) { }
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
    fn tr(&self) -> (r: u8) { 7 }
}
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn dl(&self) { self.l(); }
    fn du(&self) -> (r: u8) { let _q = self.z(); self.x() }
    proof fn dm(&self) { self.lm(); }
    fn z(&self) -> (r: u8) ensures r == self.m() && r == self.lim();
    proof fn lm(&self) ensures self.mm() == 2;
    spec fn m(&self) -> u8;
}
impl Tr for B {
    proof fn l(&self) { }
    open spec fn lim(&self) -> u8 { 7 }
    fn x(&self) -> (r: u8) { 7 }
}
impl<X: Tr> Tr for W<X> {
    open spec fn lim(&self) -> u8 { self.w.lim() }
    proof fn l(&self) { self.w.l(); }
    fn x(&self) -> (r: u8) { self.w.x() }
}
impl U for B {
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { 7 }
    open spec fn m(&self) -> u8 { 7 }
}
pub struct W<X> { pub w: X }
pub struct B { pub b: u8 }
} // verus!
