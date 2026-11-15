verus!{
impl<X: Q> Tr for S<X> { }
pub struct S<X> { pub x: X }
pub trait Q { }
pub trait Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
    proof fn lm1(&self) where T: Tr ensures self.mm() == 2;
}
impl Q for u8 { }
pub struct Z { pub z: u8 }
impl<X: Tr, T: Tr> U<T> for S<X> {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
}
} // verus!
