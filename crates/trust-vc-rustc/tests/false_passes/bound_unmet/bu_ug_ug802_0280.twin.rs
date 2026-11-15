verus!{
pub struct Z { pub z: u8 }
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Q for u8 { }
impl<X: Q> Tr for S<X> { }
impl Q for Z { }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub trait Tr { }
pub trait Q { }
pub struct S<X> { pub x: X }
} // verus!
