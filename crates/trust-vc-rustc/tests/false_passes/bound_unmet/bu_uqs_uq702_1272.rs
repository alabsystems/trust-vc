verus!{
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
}
pub struct A { pub a: u8 }
impl Tr for Z { }
pub struct B { pub b: u8 }
pub trait Tr { }
pub struct Z { pub z: u8 }
impl Tr for A { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Q: Tr { }
impl Q for A { }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
} // verus!
