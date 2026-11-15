verus!{
pub struct A { pub a: u8 } impl Q for B { }
pub trait Q { }
impl Tr for B { }
impl U<B> for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
pub trait U<T> {
    fn z0(&self) -> (r: u8) where T: Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 where T: Q { 2 }
}
} // verus!
