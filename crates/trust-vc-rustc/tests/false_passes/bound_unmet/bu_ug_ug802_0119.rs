verus!{
pub trait Tr { }
pub trait Q { }
pub struct Z { pub z: u8 }
impl U for Z {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U {
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
}
impl<X: Q> Tr for S<X> { }
pub struct S<X> { pub x: X }
} // verus!
