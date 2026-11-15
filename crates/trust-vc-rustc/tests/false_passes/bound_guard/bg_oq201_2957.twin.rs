verus!{
pub fn gz<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.z() }
impl U for A {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { self.a }
}
impl Tr for B {
    proof fn l(&self) { }
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
pub struct B { pub b: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
}
pub fn ugz() { let r = gz(&A { a: 4 }); assert(r == 4); }
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
impl U for B {
    open spec fn m(&self) -> u8 { self.b }
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { self.b }
}
pub struct A { pub a: u8 }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) { let _q = self.x(); self.z() }
    proof fn dm(&self) { }
}
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 5); }
impl Tr for A {
    proof fn l(&self) { }
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
} // verus!
