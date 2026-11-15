verus!{
pub trait Q { } impl Tr for Z { } impl Q for Z { }
pub trait U<T> {
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where T: Q { 2 }
}
pub trait Tr { }
impl<X: Q> Tr for S<X> { }
impl U<Z> for Z {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
} // verus!
