verus!{
pub trait Tr { }
impl<X, T> U<T> for S<X> {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
}
pub struct Z { pub z: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
    proof fn lm1(&self) where T: Tr ensures self.mm() == 2;
}
pub struct S<X> { pub x: X }
impl<X> Tr for S<X> { }
impl Q for u8 { }
impl<T> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) where T: Tr { 2 }
}
pub trait Q { }
} // verus!
