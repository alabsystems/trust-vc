verus!{
impl Tr for u8 { }
impl Q for Z { }
pub trait Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
}
pub struct S<X> { pub x: X }
impl U<Z> for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Q { }
impl<X> Tr for S<X> { }
impl Q for u8 { }
pub struct Z { pub z: u8 }
} // verus!
