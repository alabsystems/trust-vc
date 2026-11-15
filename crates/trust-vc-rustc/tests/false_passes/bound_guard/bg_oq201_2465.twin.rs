verus!{
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
    proof fn l(&self) { }
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dl(&self) { self.l(); }
    proof fn dm(&self) { }
}
impl U for A {
    fn z(&self) -> (r: u8) { self.a }
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
}
pub struct W<X> { pub w: X }
pub proof fn pl() ensures sp() == 1 { }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
}
impl<X: Tr> Tr for W<X> {
    fn x(&self) -> (r: u8) { self.w.x() }
    open spec fn lim(&self) -> u8 { self.w.lim() }
    proof fn l(&self) { self.w.l(); }
}
pub struct A { pub a: u8 }
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
} // verus!
