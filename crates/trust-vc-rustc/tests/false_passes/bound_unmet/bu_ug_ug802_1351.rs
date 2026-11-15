verus!{
pub struct S<X> { pub x: X }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
    fn z1(&self) -> (r: u8) where T: Tr ensures r == self.mm();
}
pub trait Q { }
impl<X, T: Q> U<T> for S<X> {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) where T: Tr { 2 }
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
}
pub trait Tr { }
impl Tr for Z { }
impl<T> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
    fn z1(&self) -> (r: u8) where T: Tr { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct Z { pub z: u8 }
} // verus!
