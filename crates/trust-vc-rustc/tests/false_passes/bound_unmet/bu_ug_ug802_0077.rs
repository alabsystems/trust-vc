verus!{
impl Q for u8 { }
pub struct Z { pub z: u8 }
impl<X, T> U<T> for S<X> {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
}
pub trait Q { }
pub struct S<X> { pub x: X }
impl Q for Z { }
impl<X: Q> Tr for S<X> { }
pub trait Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
}
} // verus!
