verus!{
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { self.a }
}
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
pub fn ugz() { let r = gz(&A { a: 4 }); assert(r == 4); }
pub struct B { pub b: u8 }
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m() && r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) ensures r == self.m() { self.z() }
    proof fn dm(&self) { self.lm(); }
}
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
pub fn gz<T: U>(t: &T) -> (r: u8) ensures r == t.m() && r == t.lim() { t.z() }
pub proof fn pl() ensures sp() == 1 { }
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
pub struct A { pub a: u8 }
} // verus!
