verus!{
pub struct S<X> { pub x: X }
impl<X: Q> Tr for S<X> { }
pub trait Q { }
pub trait Tr { }
pub struct Z { pub z: u8 }
impl Q for Z { }
impl<X, T> U<T> for S<X> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) { }
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
}
impl Q for u8 { }
} // verus!
