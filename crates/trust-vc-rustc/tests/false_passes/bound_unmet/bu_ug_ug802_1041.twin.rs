verus!{
impl<X: Q> U<X> for S<X> {
    open spec fn mm(&self) -> u8 where X: Q { 2 }
    proof fn lm0(&self) { }
}
pub trait Q { }
pub trait Tr { }
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
}
} // verus!
