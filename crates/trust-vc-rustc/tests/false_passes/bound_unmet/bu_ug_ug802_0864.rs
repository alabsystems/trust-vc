verus!{
impl<X: Q> Tr for S<X> { }
pub trait Tr { }
impl<X: Q, T> U<T> for S<X> {
    fn z1(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr { }
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where T: Tr ensures r == self.mm();
}
pub trait Q { }
pub struct S<X> { pub x: X }
impl Tr for u8 { }
pub struct Z { pub z: u8 }
} // verus!
