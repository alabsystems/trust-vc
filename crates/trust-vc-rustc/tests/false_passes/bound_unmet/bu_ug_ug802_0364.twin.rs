verus!{
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
}
pub struct S<X> { pub x: X }
impl Q for Z { }
impl<X: Q> Tr for S<X> { }
pub struct Z { pub z: u8 }
impl<X: Tr> U<X> for S<X> {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 where X: Tr { 2 }
}
impl Tr for Z { }
impl Tr for u8 { }
pub trait Tr { }
pub trait Q { }
} // verus!
