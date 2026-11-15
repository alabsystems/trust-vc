verus!{
pub trait Q { }
impl Q for u8 { }
pub trait U<T> {
    proof fn rq1(&self) where T: Q requires self.mm() == 2 ensures true;
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where T: Q { 2 }
}
impl<X: Q> Tr for S<X> { }
impl<T: Q> U<T> for Z {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
pub struct Z { pub z: u8 }
pub trait Tr { }
pub struct S<X> { pub x: X }
} // verus!
