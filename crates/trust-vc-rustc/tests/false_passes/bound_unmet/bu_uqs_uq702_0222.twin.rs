verus!{
pub struct B { pub b: u8 } impl Q for A { }
pub trait Q: Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
}
pub struct Z { pub z: u8 }
pub trait Tr { }
impl Tr for A { }
pub struct A { pub a: u8 }
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
} // verus!
