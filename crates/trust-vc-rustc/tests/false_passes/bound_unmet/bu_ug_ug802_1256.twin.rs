verus!{
pub struct S<X> { pub x: X }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where T: Tr ensures self.mm() == 2;
}
impl<T: Tr> U<T> for Z {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Tr for u8 { }
impl Tr for Z { }
pub trait Tr { }
impl<X, T> U<T> for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
    proof fn lm1(&self) where T: Tr { }
}
pub struct Z { pub z: u8 }
pub trait Q { }
impl<X: Q> Tr for S<X> { }
} // verus!
