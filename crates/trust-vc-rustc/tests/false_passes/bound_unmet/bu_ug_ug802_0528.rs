verus!{
pub trait Tr { }
impl U for Z {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Q { }
impl<X: Q> Tr for S<X> { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait U {
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
impl Q for Z { }
} // verus!
