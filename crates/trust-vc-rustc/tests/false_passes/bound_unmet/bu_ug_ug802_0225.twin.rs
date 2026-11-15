verus!{
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
impl Q for Z { }
pub trait Tr { } impl Tr for Z { }
pub trait Q { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
impl Q for u8 { }
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
impl Tr for u8 { }
impl<X: Q> Tr for S<X> { }
} // verus!
