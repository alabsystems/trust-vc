verus!{
impl Tr for A {
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
}
pub fn gx<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.x() }
pub fn ugx() { let r = gx(&A { a: 2 }); assert(r == 7); }
pub struct A { pub a: u8 }
pub proof fn pl() ensures sp() == 7 { }
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn dm(&self) { self.lm(); }
    proof fn lm(&self) ensures self.mm() == 2;
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.lim();
}
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 7); }
impl U for A {
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { 7 }
    open spec fn m(&self) -> u8 { self.a }
}
pub fn gz<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.z() }
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
pub fn ugz() { let r = gz(&A { a: 4 }); assert(r == 7); }
pub trait Tr {
    fn tr(&self) -> (r: u8) { self.x() }
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
} // verus!
