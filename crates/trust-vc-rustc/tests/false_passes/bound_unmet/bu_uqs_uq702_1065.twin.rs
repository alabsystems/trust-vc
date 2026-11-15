verus!{
impl Q for A { }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct A { pub a: u8 }
impl Tr for B { }
pub struct B { pub b: u8 }
pub trait Tr { }
impl Tr for A { }
pub struct Z { pub z: u8 }
pub trait U {
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Q: Tr { }
} // verus!
