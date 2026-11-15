verus!{
pub struct S<X> { pub x: X }
pub trait Tr { }
pub trait Q { }
impl<X: Q> Tr for S<X> { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm(&self) where Self: Tr ensures self.mm() == 2;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm(&self) where Self: Tr { }
}
} // verus!
