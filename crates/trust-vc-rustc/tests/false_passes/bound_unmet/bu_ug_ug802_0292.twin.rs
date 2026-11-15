verus!{
pub trait Tr { }
pub trait Q { }
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
}
impl<X: Tr, T: Tr> U<T> for S<X> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) { }
}
impl<X: Q> Tr for S<X> { }
} // verus!
