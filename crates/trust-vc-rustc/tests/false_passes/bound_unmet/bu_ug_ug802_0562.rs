verus!{
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    fn z0(&self) -> (r: u8) where T: Q ensures r == self.mm();
    proof fn lm1(&self) where T: Q ensures self.mm() == 2;
}
impl Q for u8 { }
pub struct S<X> { pub x: X }
pub trait Tr { }
impl Q for Z { }
pub struct Z { pub z: u8 }
pub trait Q { }
impl<X: Q> Tr for S<X> { }
impl<X: Tr> U<X> for S<X> {
    open spec fn mm(&self) -> u8 where X: Q { 2 }
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for Z { }
} // verus!
