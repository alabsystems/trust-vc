verus!{
pub fn gz<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.z() }
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 7); }
pub struct A { pub a: u8 }
impl U for A {
    fn z(&self) -> (r: u8) { 7 }
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub fn ugx() { let r = gx(&A { a: 2 }); assert(r == 7); }
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 7); }
pub fn gx<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.x() }
pub fn ugz() { let r = gz(&A { a: 4 }); assert(r == 7); }
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn z(&self) -> (r: u8) ensures r == self.lim();
    spec fn m(&self) -> u8;
    proof fn dm(&self) { self.lm(); }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { 7 }
    fn x(&self) -> (r: u8) { 7 }
}
} // verus!
