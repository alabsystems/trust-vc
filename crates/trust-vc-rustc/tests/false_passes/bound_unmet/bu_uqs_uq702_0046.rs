verus!{
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct Z { pub z: u8 }
impl Tr for B { }
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    fn dd(&self) -> (r: u8) where Self: Tr { self.z0() }
}
impl Q for Z { }
pub trait Tr { }
pub fn fB() { let _r = (B { b: 0 }).z1(); }
impl Tr for Z { }
pub fn fZ() { let _r = (Z { z: 0 }).z1(); }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Q { }
impl Q for A { }
} // verus!
