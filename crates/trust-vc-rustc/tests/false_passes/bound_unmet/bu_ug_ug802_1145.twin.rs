verus!{
pub struct S<X> { pub x: X } impl Tr for Z { } impl Q for Z { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
    fn z1(&self) -> (r: u8) where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr { 2 }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
impl<X> Tr for S<X> { }
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait Q { }
} // verus!
