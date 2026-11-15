verus!{
pub trait U {
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
impl U for B {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
impl Q for B { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
pub trait Tr { }
pub trait Q { }
} // verus!
