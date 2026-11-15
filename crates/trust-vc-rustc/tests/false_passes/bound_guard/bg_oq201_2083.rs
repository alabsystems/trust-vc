verus!{
pub use m1::*;
pub fn ugz() { let r = gz(&A { a: 4 }); assert(r == 4); }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { self.lm(); }
}
pub struct A { pub a: u8 }
pub trait Tr {
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub mod m1 {
use crate::*;
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
}
pub fn gz<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.z() }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { self.a }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
    proof fn l(&self) { }
}
} // verus!
