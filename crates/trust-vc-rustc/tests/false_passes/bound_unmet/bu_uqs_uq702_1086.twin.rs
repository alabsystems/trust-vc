verus!{
impl Q for B { }
pub fn fB() { let _r = (B { b: 0 }).z0(); }
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct Z { pub z: u8 } impl Tr for A { } impl Q for A { }
pub struct B { pub b: u8 }
pub trait Tr { }
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for B { }
impl Q for Z { }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct A { pub a: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
}
pub trait Q { }
} // verus!
