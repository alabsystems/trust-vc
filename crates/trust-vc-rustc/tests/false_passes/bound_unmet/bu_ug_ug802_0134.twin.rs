verus!{
impl<X: Tr, T: Tr> U<T> for S<X> {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
}
impl Tr for Z { }
pub trait Q { }
pub struct Z { pub z: u8 }
pub trait U<T> {
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
}
pub struct S<X> { pub x: X }
pub trait Tr { }
impl<X: Q> Tr for S<X> { }
} // verus!
