verus!{
pub trait Q { }
pub trait U {
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn dd(&self) -> (r: u8) where Self: Q { self.z0() }
}
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for A { }
pub struct A { pub a: u8 }
impl Q for A { }
pub struct B { pub b: u8 }
pub trait Tr { }
pub struct Z { pub z: u8 }
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
pub fn fA() { let _r = (A { a: 0 }).z0(); }
} // verus!
