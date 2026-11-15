verus!{
pub struct W<X> { pub w: X }
pub proof fn pl() ensures sp() == 7 { }
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
pub trait Tr {
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
impl<X: Tr> Tr for W<X> {
    proof fn l(&self) { self.w.l(); }
    fn x(&self) -> (r: u8) { self.w.x() }
    open spec fn lim(&self) -> u8 { self.w.lim() }
}
pub struct A { pub a: u8 }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { self.lm(); }
}
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
pub fn uww() { let v = W { w: W { w: A { a: 3 } } }; let r = v.x(); assert(r == 7); }
pub fn ugx() { let r = gx(&A { a: 2 }); assert(r == 7); }
pub fn gx<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.x() }
impl U for A {
    fn z(&self) -> (r: u8) { self.a }
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
    proof fn l(&self) { }
}
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
} // verus!
