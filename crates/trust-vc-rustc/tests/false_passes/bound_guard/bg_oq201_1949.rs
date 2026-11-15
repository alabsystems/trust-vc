verus!{
impl Tr for B {
    open spec fn lim(&self) -> u8 { 7 }
    fn x(&self) -> (r: u8) { 7 }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
}
impl<X: Tr> Tr for W<X> {
    open spec fn lim(&self) -> u8 { self.w.lim() }
    fn x(&self) -> (r: u8) { self.w.x() }
}
pub struct W<X> { pub w: X }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { self.lm(); }
}
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
pub struct A { pub a: u8 }
pub fn uw() { let v = W { w: A { a: 6 } }; let r = v.x(); assert(r == 7); }
pub struct B { pub b: u8 }
pub proof fn pl() ensures sp() == 7 { }
impl U for A {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { self.a }
}
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
} // verus!
