verus!{
impl Q for Z { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where T: Q ensures r == self.mm();
}
pub trait Q { }
impl Tr for u8 { }
pub trait Tr { }
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
impl<X, T: Tr> U<T> for S<X> {
    proof fn lm0(&self) where T: Q { }
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
} // verus!
