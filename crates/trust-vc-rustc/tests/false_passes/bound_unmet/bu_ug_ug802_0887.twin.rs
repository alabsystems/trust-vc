verus!{
impl<X: Q> Tr for S<X> { }
pub struct Z { pub z: u8 } impl Tr for Z { } impl Q for Z { }
pub trait Q { }
impl U for Z {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub struct S<X> { pub x: X }
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
impl Q for u8 { }
impl<X> U for S<X> {
    fn z1(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
} // verus!
