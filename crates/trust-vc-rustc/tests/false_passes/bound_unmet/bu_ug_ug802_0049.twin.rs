verus!{
pub trait U<T> {
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm1(&self) where T: Tr ensures self.mm() == 2;
}
impl<X: Tr, T: Tr> U<T> for S<X> {
    proof fn lm1(&self) where T: Tr { }
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct S<X> { pub x: X }
impl<X> Tr for S<X> { }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
} // verus!
