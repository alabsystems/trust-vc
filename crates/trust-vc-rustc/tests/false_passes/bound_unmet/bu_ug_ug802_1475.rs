verus!{
impl<X> Tr for S<X> { }
impl Tr for u8 { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
}
pub struct Z { pub z: u8 }
impl U<Z> for Z {
    proof fn lm0(&self) { }
}
impl Q for Z { }
pub trait Q { }
impl<X: Q> U<Z> for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub struct S<X> { pub x: X }
pub trait Tr { }
} // verus!
