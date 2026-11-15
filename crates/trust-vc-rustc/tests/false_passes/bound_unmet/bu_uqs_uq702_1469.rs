verus!{
impl Tr for Z { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U {
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
}
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Q { }
pub fn fB() { let _r = (B { b: 0 }).z0(); }
pub struct A { pub a: u8 }
impl Q for Z { }
impl Q for B { }
pub struct Z { pub z: u8 }
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
pub struct B { pub b: u8 }
} // verus!
