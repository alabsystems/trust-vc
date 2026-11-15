verus!{
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { self.a }
}
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
pub struct B { pub b: u8 }
impl Tr for B {
    fn x(&self) -> (r: u8) { 7 }
    proof fn l(&self) { }
    open spec fn lim(&self) -> u8 { 7 }
}
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.m();
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { }
    spec fn m(&self) -> u8;
}
impl U for B {
    fn z(&self) -> (r: u8) { self.b }
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.b }
}
pub struct A { pub a: u8 }
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
impl Tr for A {
    proof fn l(&self) { }
    open spec fn lim(&self) -> u8 { 7 }
    fn x(&self) -> (r: u8) { 7 }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
}
} // verus!
