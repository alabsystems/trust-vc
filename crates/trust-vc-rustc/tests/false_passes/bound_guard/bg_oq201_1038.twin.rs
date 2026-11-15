verus!{
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 5); }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) { self.x() }
    proof fn dl(&self) { self.l(); }
    proof fn dm(&self) { }
}
pub fn gz<T: U>(t: &T) -> (r: u8) ensures r == t.m() { t.z() }
pub struct A { pub a: u8 }
impl U for A {
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { self.a }
    open spec fn m(&self) -> u8 { self.a }
}
pub fn ugz() { let r = gz(&A { a: 4 }); assert(r == 4); }
impl Tr for A {
    proof fn l(&self) { }
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
}
} // verus!
