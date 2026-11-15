verus!{
impl Tr for B { }
pub trait Tr { }
impl Tr for A { }
impl Q for B { }
impl Q for Z { }
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    fn dd(&self) -> (r: u8) where Self: Q { self.z0() }
}
impl Tr for Z { }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Q: Tr { }
} // verus!
