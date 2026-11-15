verus!{
pub trait Tr { }
pub trait U {
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
}
pub struct Z { pub z: u8 }
pub trait Q { }
impl<X> Tr for S<X> { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
pub struct S<X> { pub x: X }
} // verus!
