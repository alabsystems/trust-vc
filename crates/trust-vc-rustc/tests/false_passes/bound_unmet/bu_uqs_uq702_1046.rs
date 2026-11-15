verus!{
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
pub trait U {
    fn dd(&self) -> (r: u8) where Self: Q { self.z0() }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
}
pub struct B { pub b: u8 }
impl Tr for A { }
pub trait Tr { }
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
impl U for Z {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
impl Q for A { }
pub trait Q { }
} // verus!
