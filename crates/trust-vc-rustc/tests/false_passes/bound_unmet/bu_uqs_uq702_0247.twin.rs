verus!{
pub struct A { pub a: u8 }
impl Q for B { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for Z { }
impl Q for Z { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    fn dd(&self) -> (r: u8) where Self: Tr { self.z0() }
}
pub struct B { pub b: u8 }
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
pub fn fB() { let _r = (B { b: 0 }).z0(); }
pub struct Z { pub z: u8 }
pub trait Q: Tr { }
pub trait Tr { }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for B { }
} // verus!
