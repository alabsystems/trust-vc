verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
impl<T: Tr> U<T> for Z {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    fn z1(&self) -> (r: u8) where T: Q { 2 }
}
impl<X> Tr for S<X> { }
pub trait U<T> {
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where T: Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 where T: Q { 2 }
}
pub trait Q { }
} // verus!
