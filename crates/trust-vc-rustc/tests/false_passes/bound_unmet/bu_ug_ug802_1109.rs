verus!{
pub trait Q { }
pub struct Z { pub z: u8 }
impl Q for u8 { }
impl Tr for Z { }
impl<X: Q> Tr for S<X> { }
pub struct S<X> { pub x: X }
impl Q for Z { }
impl<X: Tr, T> U<T> for S<X> {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
}
pub trait U<T> {
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
}
pub trait Tr { }
impl U<u8> for Z {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
} // verus!
