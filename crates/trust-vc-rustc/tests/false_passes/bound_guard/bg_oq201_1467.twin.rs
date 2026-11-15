verus!{
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dl(&self) { self.l(); }
    proof fn dm(&self) { }
}
pub trait Tr {
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
pub struct B { pub b: u8 }
impl U for A {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { self.a }
}
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 7); }
impl Tr for A {
    proof fn l(&self) { }
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
}
impl Tr for B {
    open spec fn lim(&self) -> u8 { 7 }
    fn x(&self) -> (r: u8) { 7 }
    proof fn l(&self) { }
}
pub fn ugx() { let r = gx(&A { a: 2 }); assert(r == 7); }
pub fn gx<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.x() }
pub struct A { pub a: u8 }
} // verus!
