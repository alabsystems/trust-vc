verus!{
impl U for Z {
    proof fn rq0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
impl Tr for A { }
impl Q for Z { }
impl Q for A { }
pub struct Z { pub z: u8 }
pub trait Q { }
pub struct A { pub a: u8 }
pub trait Tr { }
impl Q for B { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn rq0(&self) where Self: Tr + Q requires self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
}
pub mod m2 {
use crate::*;
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn rq0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
}
pub struct B { pub b: u8 }
impl U for B {
    proof fn rq0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
} // verus!
