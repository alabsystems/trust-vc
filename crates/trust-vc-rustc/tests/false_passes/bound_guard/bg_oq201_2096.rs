verus!{
pub struct W<X> { pub w: X }
pub fn gz<T: U>(t: &T) -> (r: u8) ensures r == t.m() && r == t.lim() { t.z() }
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
pub fn uw() { let v = W { w: A { a: 6 } }; let r = v.x(); assert(r == 6); }
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.m() && r == self.lim();
    proof fn dm(&self) { self.lm(); }
    proof fn lm(&self) ensures self.mm() == 2;
    spec fn m(&self) -> u8;
}
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub fn ugz() { let r = gz(&A { a: 4 }); assert(r == 4); }
impl U for A {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { self.a }
}
pub struct A { pub a: u8 }
impl<X: Tr> Tr for W<X> {
    open spec fn lim(&self) -> u8 { self.w.lim() }
    fn x(&self) -> (r: u8) { self.w.x() }
}
} // verus!
