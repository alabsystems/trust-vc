verus!{
pub trait Tr { }
pub struct S<X> { pub x: X }
impl<X: Q> Tr for S<X> { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
}
pub trait Q { }
pub struct Z { pub z: u8 }
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
} // verus!
