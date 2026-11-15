verus!{
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 5); }
pub trait U: Tr {
    fn z(&self) -> (r: u8) ensures r == self.m() && r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    spec fn m(&self) -> u8;
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { }
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { self.a }
    proof fn lm(&self) { }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
    proof fn l(&self) { }
}
pub fn gx<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.x() }
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    proof fn l(&self) { }
    fn x(&self) -> (r: u8) { self.b }
}
pub fn ugx() { let r = gx(&A { a: 2 }); assert(r == 2); }
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
}
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
} // verus!
