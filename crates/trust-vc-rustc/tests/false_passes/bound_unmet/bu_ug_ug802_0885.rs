verus!{
pub struct S<X> { pub x: X }
impl U<Z> for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
impl<X> U<X> for S<X> {
    open spec fn mm(&self) -> u8 where X: Q { 2 }
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
impl Q for u8 { }
pub trait Tr { }
pub trait Q { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
}
} // verus!
