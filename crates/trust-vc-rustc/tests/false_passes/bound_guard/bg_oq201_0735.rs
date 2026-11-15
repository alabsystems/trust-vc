verus!{
pub struct A { pub a: u8 }
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m() && r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) { self.x() }
    proof fn dm(&self) { self.lm(); }
}
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
pub struct W<X> { pub w: X }
impl U for A {
    fn du(&self) -> (r: u8) { self.a }
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { self.a }
}
impl<X: Tr> Tr for W<X> {
    open spec fn lim(&self) -> u8 { self.w.lim() }
    fn x(&self) -> (r: u8) { self.w.x() }
}
} // verus!
