verus!{
impl Tr for u8 { }
impl<X> U<X> for S<X> {
    proof fn rq0(&self) where X: Tr { assert(self.mm() == 2); }
    fn z1(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 where X: Tr { 2 }
}
pub struct S<X> { pub x: X }
pub trait Tr { }
pub trait Q { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn rq0(&self) where T: Tr requires self.mm() == 2 ensures true;
    fn z1(&self) -> (r: u8) where T: Tr ensures r == self.mm();
}
pub struct Z { pub z: u8 }
impl<X> Tr for S<X> { }
} // verus!
