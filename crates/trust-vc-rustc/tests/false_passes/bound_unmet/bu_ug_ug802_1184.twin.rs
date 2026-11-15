verus!{
pub trait Tr { }
impl Tr for Z { }
impl Q for u8 { }
pub struct S<X> { pub x: X }
impl Q for Z { }
impl<X: Q> Tr for S<X> { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm1(&self) where T: Q ensures self.mm() == 2;
    proof fn rq0(&self) where T: Q requires self.mm() == 2 ensures true;
}
pub struct Z { pub z: u8 }
pub trait Q { }
impl<T: Q> U<T> for Z {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
    open spec fn mm(&self) -> u8 where T: Q { 2 }
}
} // verus!
