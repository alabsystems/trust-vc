verus!{
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 5); }
pub struct A { pub a: u8 }
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    proof fn l(&self) { }
    fn x(&self) -> (r: u8) { self.b }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
    fn tr(&self) -> (r: u8) { self.x() }
}
pub struct B { pub b: u8 }
pub trait U: Tr {
    proof fn lm(&self) ensures self.mm() == 2;
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn dm(&self) { self.lm(); }
    fn du(&self) -> (r: u8) { self.z() }
    proof fn dl(&self) { self.l(); }
}
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
impl U for A {
    fn z(&self) -> (r: u8) { self.a }
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
impl Tr for A {
    proof fn l(&self) { }
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
} // verus!
