verus!{
pub trait Tr { }
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct B { pub b: u8 }
impl Tr for A { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    fn dd(&self) -> (r: u8) where Self: Q { self.z0() }
}
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Q: Tr { }
pub struct A { pub a: u8 }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct Z { pub z: u8 }
} // verus!
