verus!{
impl Tr for A {
    open spec fn lim(&self) -> u8 { 7 }
    fn x(&self) -> (r: u8) { 7 }
}
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 7); }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
pub struct A { pub a: u8 }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) { self.x() }
    proof fn dm(&self) { self.lm(); }
}
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 7); }
impl U for A {
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { 7 }
    open spec fn m(&self) -> u8 { self.a }
}
} // verus!
