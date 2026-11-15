verus!{
impl U<Z> for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
impl Q for u8 { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where T: Tr ensures self.mm() == 2;
}
pub trait Tr { }
impl Q for Z { }
impl<X: Q> Tr for S<X> { }
pub trait Q { }
impl<X, T: Q> U<T> for S<X> {
    proof fn lm1(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
} // verus!
