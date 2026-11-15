verus!{
impl Q for Z { }
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait U<T> {
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm1(&self) where T: Tr ensures self.mm() == 2;
}
impl<X: Q, T> U<T> for S<X> {
    proof fn lm1(&self) { }
    proof fn lm0(&self) where T: Tr { }
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
}
pub struct S<X> { pub x: X }
pub trait Q { }
impl<X> Tr for S<X> { }
} // verus!
