verus!{
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m() && r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { self.lm(); }
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { self.a }
}
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 5); }
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub fn gz<T: U>(t: &T) -> (r: u8) ensures r == t.m() && r == t.lim() { t.z() }
pub fn ugx() { let r = gx(&A { a: 2 }); assert(r == 2); }
pub proof fn pl() ensures sp() == 1 { }
pub fn ugz() { let r = gz(&A { a: 4 }); assert(r == 4); }
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
pub fn gx<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.x() }
} // verus!
