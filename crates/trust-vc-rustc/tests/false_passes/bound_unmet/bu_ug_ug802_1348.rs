verus!{
impl<X: Q, T> U<T> for S<X> {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm1(&self) { }
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    proof fn lm1(&self) where T: Q ensures self.mm() == 2;
}
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
} // verus!
