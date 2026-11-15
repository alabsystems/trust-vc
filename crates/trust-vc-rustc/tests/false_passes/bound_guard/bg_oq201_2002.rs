verus!{
pub fn ugz() { let r = gz(&A { a: 4 }); assert(r == 7); }
pub struct A { pub a: u8 }
impl Tr for A {
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
    proof fn l(&self) { }
}
impl U for A {
    fn z(&self) -> (r: u8) { 7 }
    open spec fn m(&self) -> u8 { 7 }
    proof fn lm(&self) { }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m() && r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) ensures r == self.m() { self.z() }
    proof fn dl(&self) { self.l(); }
    proof fn dm(&self) { self.lm(); }
}
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 7); }
pub fn gz<T: U>(t: &T) -> (r: u8) ensures r == t.m() && r == t.lim() { t.z() }
} // verus!
