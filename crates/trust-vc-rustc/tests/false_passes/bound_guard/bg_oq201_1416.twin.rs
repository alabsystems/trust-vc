verus!{
pub struct A { pub a: u8 }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dl(&self) { self.l(); }
    proof fn dm(&self) { }
}
pub fn gz<T: U>(t: &T) -> (r: u8) ensures r == t.m() { t.z() }
pub fn ugz() { let r = gz(&A { a: 4 }); assert(r == 4); }
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
impl U for A {
    fn z(&self) -> (r: u8) { self.a }
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { 7 }
    proof fn l(&self) { }
    fn x(&self) -> (r: u8) { 7 }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
}
} // verus!
