verus!{
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct B { pub b: u8 }
impl Tr for Z { }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
pub trait Q: Tr { }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
} // verus!
