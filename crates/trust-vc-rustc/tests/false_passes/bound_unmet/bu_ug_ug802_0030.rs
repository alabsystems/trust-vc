verus!{
pub trait U {
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait Tr { }
impl<X: Q> Tr for S<X> { }
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
impl Q for u8 { }
pub trait Q { }
} // verus!
