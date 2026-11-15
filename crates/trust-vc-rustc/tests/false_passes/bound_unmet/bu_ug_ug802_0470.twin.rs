verus!{
impl<X: Q, T: Q> U<T> for S<X> {
    proof fn rq1(&self) where T: Q { }
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 where T: Q { 2 }
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    proof fn rq1(&self) where T: Q requires self.mm() == 2 ensures true;
}
pub trait Tr { }
impl Tr for u8 { }
pub trait Q { }
impl Q for Z { }
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
} // verus!
