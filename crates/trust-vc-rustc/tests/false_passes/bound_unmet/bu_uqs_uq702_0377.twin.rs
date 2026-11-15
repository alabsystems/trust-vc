verus!{
impl U<B> for B {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
impl Q for A { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
}
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub trait Q: Tr { }
impl Tr for A { }
impl U<A> for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct Z { pub z: u8 }
} // verus!
