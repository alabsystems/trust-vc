verus!{
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m() && r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) ensures r == self.m() { self.z() }
    proof fn dm(&self) { }
}
pub struct A { pub a: u8 }
impl U for A {
    fn du(&self) -> (r: u8) { self.a }
    fn z(&self) -> (r: u8) { self.a }
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
pub fn gz<T: U>(t: &T) -> (r: u8) ensures r == t.m() && r == t.lim() { t.z() }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub fn ugz() { let r = gz(&A { a: 4 }); assert(r == 4); }
} // verus!
