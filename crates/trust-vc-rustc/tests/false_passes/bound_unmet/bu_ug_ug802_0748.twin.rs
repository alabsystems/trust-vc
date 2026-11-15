verus!{
pub struct Z { pub z: u8 } impl Tr for Z { } impl Q for Z { }
pub struct S<X> { pub x: X }
pub trait Tr { }
pub trait Q { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    fn z0(&self) -> (r: u8) where T: Q ensures r == self.mm();
    proof fn rq1(&self) where T: Q requires self.mm() == 2 ensures true;
}
impl<X: Q> Tr for S<X> { }
impl U<Z> for Z {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn rq1(&self) { }
}
impl Tr for u8 { }
} // verus!
