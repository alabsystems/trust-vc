verus!{
impl Tr for B {
    open spec fn lim(&self) -> u8 { 7 }
    fn x(&self) -> (r: u8) { 7 }
}
impl U for A {
    fn z(&self) -> (r: u8) { self.a }
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
}
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 7); }
pub trait U: Tr {
    proof fn lm(&self) ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.m();
    proof fn dm(&self) { self.lm(); }
    fn du(&self) -> (r: u8) { self.z() }
    spec fn m(&self) -> u8;
}
pub struct A { pub a: u8 }
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
pub struct B { pub b: u8 }
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
impl Tr for A {
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
}
impl U for B {
    fn z(&self) -> (r: u8) { self.b }
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.b }
}
} // verus!
