verus!{
pub struct Z { pub z: u8 }
impl<X: Q> Tr for S<X> { }
impl<X, T: Tr> U<T> for S<X> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
impl Q for Z { }
impl Q for u8 { }
pub struct S<X> { pub x: X }
pub trait Q { }
pub trait Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    fn z0(&self) -> (r: u8) where T: Q ensures r == self.mm();
}
impl Tr for u8 { }
} // verus!
