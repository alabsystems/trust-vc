verus!{
pub trait Tr { }
impl Tr for B { }
impl Tr for A { }
pub trait U {
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
}
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct Z { pub z: u8 }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
impl Q for B { }
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub trait Q: Tr { }
} // verus!
