verus!{
pub trait Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
    proof fn rq1(&self) where T: Tr requires self.mm() == 2 ensures true;
}
impl<T: Tr> U<T> for Z {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    fn z0(&self) -> (r: u8) { 2 }
    proof fn rq1(&self) { }
}
pub struct Z { pub z: u8 }
pub trait Q { }
impl<X: Q> Tr for S<X> { }
pub struct S<X> { pub x: X }
} // verus!
