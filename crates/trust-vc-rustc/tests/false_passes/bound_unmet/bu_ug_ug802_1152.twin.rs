verus!{
impl<X: Q> Tr for S<X> { }
impl Q for Z { }
pub trait Tr { }
pub trait Q { }
pub struct S<X> { pub x: X }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
impl Tr for u8 { }
impl<X: Q> U for S<X> {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub struct Z { pub z: u8 }
} // verus!
