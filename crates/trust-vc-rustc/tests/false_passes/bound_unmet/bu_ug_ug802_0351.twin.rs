verus!{
pub trait Tr { } impl Tr for Z { }
impl<X: Tr> U for S<X> {
    proof fn lm1(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Q { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
}
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
impl Q for Z { }
} // verus!
