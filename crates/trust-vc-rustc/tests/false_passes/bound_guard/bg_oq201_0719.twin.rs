verus!{
pub struct A { pub a: u8 }
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
impl U for B {
    open spec fn m(&self) -> u8 { self.b }
    fn z(&self) -> (r: u8) { self.b }
    proof fn lm(&self) { }
    fn du(&self) -> (r: u8) { self.b }
}
pub struct B { pub b: u8 }
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 5); }
pub trait U: Tr {
    fn du(&self) -> (r: u8) { let _q = self.z(); self.x() }
    proof fn lm(&self) ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
    proof fn dm(&self) { }
    fn z(&self) -> (r: u8) ensures r == self.lim();
    spec fn m(&self) -> u8;
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    fn du(&self) -> (r: u8) { self.a }
    fn z(&self) -> (r: u8) { self.a }
    proof fn lm(&self) { }
}
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub proof fn pl() ensures sp() == 1 { }
} // verus!
