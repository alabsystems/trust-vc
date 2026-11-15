verus!{
pub fn ugx() { let r = gx(&A { a: 2 }); assert(r == 2); }
impl U for B {
    open spec fn m(&self) -> u8 { self.b }
    fn z(&self) -> (r: u8) { self.b }
    proof fn lm(&self) { }
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    proof fn dl(&self) { self.l(); }
    fn z(&self) -> (r: u8) ensures r == self.m();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
}
impl Tr for A {
    proof fn l(&self) { }
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub struct A { pub a: u8 }
pub fn gx<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.x() }
impl<X: Tr> Tr for W<X> {
    open spec fn lim(&self) -> u8 { self.w.lim() }
    proof fn l(&self) { self.w.l(); }
    fn x(&self) -> (r: u8) { self.w.x() }
}
pub struct W<X> { pub w: X }
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
    proof fn l(&self) { }
}
impl U for A {
    fn z(&self) -> (r: u8) { self.a }
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
pub struct B { pub b: u8 }
} // verus!
