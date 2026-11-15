verus!{
pub trait Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
}
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
pub trait Q { }
impl<X> Tr for S<X> { }
impl Q for u8 { }
impl<X: Q, T: Q> U<T> for S<X> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) { }
}
} // verus!
