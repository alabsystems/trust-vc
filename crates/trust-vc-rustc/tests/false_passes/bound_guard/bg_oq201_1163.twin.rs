verus!{
pub use m1::*;
pub use m1::m2::*;
pub fn ugz() { let r = gz(&A { a: 4 }); assert(r == 7); }
pub mod m1 {
use crate::*;
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 7); }
pub fn gz<T: U>(t: &T) -> (r: u8) ensures r == t.m() && r == t.lim() { t.z() }
pub mod m2 {
use crate::*;
impl U for A {
    fn du(&self) -> (r: u8) { 7 }
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { 7 }
    open spec fn m(&self) -> u8 { 7 }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
}
}
impl Tr for B {
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
}
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 7); }
pub struct A { pub a: u8 }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m() && r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) { let _q = self.z(); self.x() }
    proof fn dm(&self) { }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { 7 }
    fn x(&self) -> (r: u8) { 7 }
}
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
pub struct B { pub b: u8 }
} // verus!
