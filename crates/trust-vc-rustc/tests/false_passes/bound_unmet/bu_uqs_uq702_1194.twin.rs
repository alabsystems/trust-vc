verus!{
impl Tr for B { }
pub struct Z { pub z: u8 }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
impl Q for B { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct A { pub a: u8 }
pub trait Q: Tr { }
pub trait U {
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 { 2 }
}
impl Tr for Z { }
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for A { }
pub fn fB() { let _r = (B { b: 0 }).z0(); }
impl Q for A { }
pub struct B { pub b: u8 }
pub trait Tr { }
} // verus!
