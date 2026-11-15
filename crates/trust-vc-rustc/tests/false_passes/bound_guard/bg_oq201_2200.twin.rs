verus!{
pub struct A { pub a: u8 }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { self.a }
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) ensures r == self.lim() { self.z() }
    proof fn dm(&self) { }
}
impl Tr for A {
    proof fn l(&self) { }
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub fn ugx() { let r = gx(&A { a: 2 }); assert(r == 2); }
pub fn gx<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.x() }
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 5); }
pub fn gz<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.z() }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
    fn tr(&self) -> (r: u8) { self.x() }
}
pub struct B { pub b: u8 }
impl Tr for B {
    proof fn l(&self) { }
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
pub fn ugz() { let r = gz(&A { a: 4 }); assert(r == 4); }
} // verus!
