verus!{
pub trait Q { }
pub struct Z { pub z: u8 }
impl Q for Z { }
impl<X> U<X> for S<X> {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 where X: Q { 2 }
    proof fn lm1(&self) where X: Q { }
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    proof fn lm1(&self) where T: Q ensures self.mm() == 2;
}
impl Tr for u8 { }
impl Tr for Z { }
pub struct S<X> { pub x: X }
pub trait Tr { }
} // verus!
