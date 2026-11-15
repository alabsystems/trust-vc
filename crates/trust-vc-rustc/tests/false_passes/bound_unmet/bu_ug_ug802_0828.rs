verus!{
pub struct Z { pub z: u8 }
impl<X: Q> Tr for S<X> { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
}
pub struct S<X> { pub x: X }
pub trait Tr { }
impl U<u8> for Z {
    proof fn lm0(&self) { }
}
pub trait Q { }
} // verus!
