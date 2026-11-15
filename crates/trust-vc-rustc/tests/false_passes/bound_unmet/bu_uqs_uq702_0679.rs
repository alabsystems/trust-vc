verus!{
pub mod m2 {
use crate::*;
impl Tr for A { }
}
impl U for A {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn rq1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U {
    proof fn rq1(&self) where Self: Tr + Q requires self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
}
pub mod m1 {
use crate::*;
impl Q for Z { }
}
pub struct B { pub b: u8 }
pub trait Tr { }
impl U for Z {
    proof fn rq1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub trait Q { }
} // verus!
