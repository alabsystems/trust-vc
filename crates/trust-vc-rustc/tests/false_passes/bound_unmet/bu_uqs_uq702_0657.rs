verus!{
pub struct B { pub b: u8 }
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for B { }
pub struct Z { pub z: u8 }
impl Q for A { }
impl Q for B { }
pub trait Q { }
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    fn dd(&self) -> (r: u8) where Self: Tr { self.z0() }
}
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct A { pub a: u8 }
} // verus!
