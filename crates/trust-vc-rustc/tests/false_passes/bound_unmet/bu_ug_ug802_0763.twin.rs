verus!{
impl<X: Q> Tr for S<X> { }
pub trait Q { }
impl Q for Z { }
impl Tr for u8 { }
pub struct Z { pub z: u8 }
pub trait Tr { }
impl Tr for Z { }
pub trait U<T> {
    proof fn lm1(&self) where T: Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
}
impl<X: Q> U<X> for S<X> {
    proof fn lm1(&self) { }
    open spec fn mm(&self) -> u8 where X: Q { 2 }
    proof fn lm0(&self) where X: Q { }
}
pub struct S<X> { pub x: X }
} // verus!
