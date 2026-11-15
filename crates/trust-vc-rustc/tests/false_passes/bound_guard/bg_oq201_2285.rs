verus!{
pub fn ugz() { let r = gz(&A { a: 4 }); assert(r == 4); }
impl Tr for B {
    proof fn l(&self) { }
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
pub struct B { pub b: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
}
impl U for B {
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { self.x() }
    open spec fn m(&self) -> u8 { self.b }
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { self.a }
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) { let _q = self.x(); self.z() }
    proof fn dm(&self) { self.lm(); }
}
pub fn gz<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.z() }
pub struct A { pub a: u8 }
impl Tr for A {
    proof fn l(&self) { }
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
} // verus!
