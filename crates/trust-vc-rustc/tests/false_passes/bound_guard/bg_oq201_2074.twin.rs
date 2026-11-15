verus!{
impl Tr for A {
    open spec fn lim(&self) -> u8 { 7 }
    fn x(&self) -> (r: u8) { 7 }
}
pub struct A { pub a: u8 }
impl U for A {
    fn z(&self) -> (r: u8) { self.a }
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
    fn du(&self) -> (r: u8) { self.a }
}
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
pub proof fn pl() ensures sp() == 7 { }
pub trait U: Tr {
    proof fn lm(&self) ensures self.mm() == 2;
    fn z(&self) -> (r: u8) ensures r == self.m();
    fn du(&self) -> (r: u8) { self.z() }
    open spec fn mm(&self) -> u8 { 2 }
    spec fn m(&self) -> u8;
    proof fn dm(&self) { }
}
} // verus!
