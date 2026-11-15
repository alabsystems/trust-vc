verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    proof fn rq1(&self) where T: Tr requires self.mm() == 2 ensures true;
}
impl<X: Tr, T: Tr> U<T> for S<X> {
    proof fn rq1(&self) where T: Tr { }
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
}
pub trait Tr { }
pub trait Q { }
impl Q for u8 { }
impl Q for Z { }
impl<X: Q> Tr for S<X> { }
} // verus!
