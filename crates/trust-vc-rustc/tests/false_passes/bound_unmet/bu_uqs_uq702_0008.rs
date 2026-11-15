verus!{
pub trait Q { }
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for B { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
}
pub trait Tr { }
impl Tr for A { }
impl Q for B { }
pub fn fB() { let _r = (B { b: 0 }).z0(); }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
impl Q for A { }
pub fn fA() { let _r = (A { a: 0 }).z0(); }
} // verus!
