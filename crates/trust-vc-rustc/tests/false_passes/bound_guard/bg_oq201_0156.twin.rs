verus!{
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dl(&self) { self.l(); }
    proof fn dm(&self) { }
}
impl Tr for A {
    proof fn l(&self) { }
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
}
impl U for A {
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { 7 }
    open spec fn m(&self) -> u8 { self.a }
}
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 7); }
pub proof fn pl() ensures sp() == 7 { }
pub struct A { pub a: u8 }
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
}
} // verus!
