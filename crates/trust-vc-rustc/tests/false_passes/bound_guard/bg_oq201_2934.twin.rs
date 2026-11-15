verus!{
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
pub proof fn pl() ensures sp() == 1 { }
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
impl U for A {
    fn z(&self) -> (r: u8) { self.a }
    fn du(&self) -> (r: u8) { self.a }
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
}
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 5); }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m() && r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) { let _q = self.x(); self.z() }
    proof fn dm(&self) { }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub struct A { pub a: u8 }
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
} // verus!
