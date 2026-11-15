verus!{
pub trait Q { }
pub trait U {
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
impl<X: Q> Tr for S<X> { }
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct S<X> { pub x: X }
pub trait Tr { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct Z { pub z: u8 }
impl Tr for u8 { }
} // verus!
