verus!{
pub trait Q { }
pub trait U {
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub struct Z { pub z: u8 }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
pub struct A { pub a: u8 }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for Z { }
impl Q for A { }
pub struct B { pub b: u8 }
} // verus!
