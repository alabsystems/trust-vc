verus!{
pub struct S<X> { pub x: X }
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
impl<X: Q> Tr for S<X> { }
impl<X> U for S<X> {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait Q { }
} // verus!
