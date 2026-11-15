verus!{
impl<T: Q> U<T> for Z {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
impl<X> Tr for S<X> { }
impl Tr for Z { }
pub trait Q { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where T: Q ensures r == self.mm();
}
pub trait Tr { }
impl<X: Q, T: Q> U<T> for S<X> {
    fn z1(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q { }
}
} // verus!
