verus!{
pub struct Z { pub z: u8 } impl Q for u8 { }
impl<X: Q> Tr for S<X> { }
impl Tr for u8 { }
pub trait Q { }
pub trait Tr { }
impl Tr for Z { }
impl U<u8> for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct S<X> { pub x: X }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    fn z0(&self) -> (r: u8) where T: Q ensures r == self.mm();
}
} // verus!
