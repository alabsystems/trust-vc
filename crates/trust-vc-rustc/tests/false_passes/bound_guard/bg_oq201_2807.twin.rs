verus!{
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { }
    fn z(&self) -> (r: u8) ensures r == self.m();
    spec fn m(&self) -> u8;
}
pub fn ugz() { let r = gz(&A { a: 4 }); assert(r == 4); }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { self.a }
    proof fn lm(&self) { }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { 7 }
    fn x(&self) -> (r: u8) { 7 }
}
pub struct B { pub b: u8 }
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
pub struct A { pub a: u8 }
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 7); }
impl Tr for B {
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
}
pub fn gz<T: U>(t: &T) -> (r: u8) ensures r == t.m() { t.z() }
} // verus!
