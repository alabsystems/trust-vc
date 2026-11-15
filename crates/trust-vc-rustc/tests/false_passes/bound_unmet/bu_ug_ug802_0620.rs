verus!{
pub trait Q { }
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
    fn z1(&self) -> (r: u8) where T: Tr ensures r == self.mm();
}
impl<X> Tr for S<X> { }
impl Q for u8 { }
impl<T: Q> U<T> for Z {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
} // verus!
