verus!{
impl U for A {
    fn z(&self) -> (r: u8) { 7 }
    open spec fn m(&self) -> u8 { 7 }
    proof fn lm(&self) { }
}
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.m() && r == self.lim();
    fn du(&self) -> (r: u8) { 2 }
    spec fn m(&self) -> u8;
    proof fn dm(&self) { self.lm(); }
    proof fn lm(&self) ensures self.mm() == 2;
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { 7 }
    fn x(&self) -> (r: u8) { 7 }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 7); }
impl Tr for B {
    open spec fn lim(&self) -> u8 { 7 }
    fn x(&self) -> (r: u8) { 7 }
}
} // verus!
