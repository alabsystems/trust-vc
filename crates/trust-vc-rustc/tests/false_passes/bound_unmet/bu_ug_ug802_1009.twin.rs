verus!{
impl Tr for Z { }
impl<X: Q> Tr for S<X> { }
pub struct S<X> { pub x: X }
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
}
impl<X: Q> U for S<X> {
    proof fn lm1(&self) where Self: Tr { }
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait Q { }
pub struct Z { pub z: u8 }
} // verus!
