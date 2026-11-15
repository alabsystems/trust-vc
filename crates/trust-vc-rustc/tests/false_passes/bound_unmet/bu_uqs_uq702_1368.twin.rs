verus!{
pub struct A { pub a: u8 } impl Tr for Z { } impl Q for Z { }
pub trait Q: Tr { }
impl Tr for B { }
pub struct Z { pub z: u8 }
pub trait U<T> {
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
    fn dd(&self) -> (r: u8) where T: Tr { self.z1() }
    fn z1(&self) -> (r: u8) where T: Tr ensures r == self.mm();
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
}
pub struct B { pub b: u8 }
impl U<B> for B {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
impl U<Z> for A {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
} // verus!
