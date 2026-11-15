verus!{
pub trait Tr { }
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub trait Q: Tr { }
impl Tr for A { }
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    fn dd(&self) -> (r: u8) where Self: Q { self.z0() }
}
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
} // verus!
