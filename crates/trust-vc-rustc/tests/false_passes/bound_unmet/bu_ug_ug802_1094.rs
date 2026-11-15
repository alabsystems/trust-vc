verus!{
impl<X: Q> Tr for S<X> { }
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
impl Tr for Z { }
pub trait Q { }
pub trait Tr { }
pub trait U {
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
}
} // verus!
