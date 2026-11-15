verus!{
pub trait Tr { }
impl<X: Q> Tr for S<X> { }
pub trait U<T> {
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where T: Q { 2 }
}
pub trait Q { }
pub struct Z { pub z: u8 }
impl Q for Z { }
impl U<u8> for Z {
    proof fn lm0(&self) { }
}
impl Tr for Z { }
pub struct S<X> { pub x: X }
} // verus!
