verus!{
impl Tr for A { }
impl Tr for Z { }
impl Q for Z { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait Tr { } impl Q for A { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
}
pub fn fZ() { let _r = (Z { z: 0 }).z1(); }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
pub trait Q: Tr { }
pub struct A { pub a: u8 }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
} // verus!
