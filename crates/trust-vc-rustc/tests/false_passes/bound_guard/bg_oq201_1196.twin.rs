verus!{
impl U for B {
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { 7 }
    open spec fn m(&self) -> u8 { self.b }
}
impl Tr for B {
    proof fn l(&self) { }
    open spec fn lim(&self) -> u8 { 7 }
    fn x(&self) -> (r: u8) { 7 }
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { self.x() }
}
pub struct A { pub a: u8 }
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 7); }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
    fn tr(&self) -> (r: u8) ensures r == self.lim() { self.x() }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { 7 }
    fn x(&self) -> (r: u8) { let _q = (B { b: 1 }).z(); 7 }
    proof fn l(&self) { }
}
pub proof fn pl() ensures sp() == 7 { }
pub struct B { pub b: u8 }
} // verus!
