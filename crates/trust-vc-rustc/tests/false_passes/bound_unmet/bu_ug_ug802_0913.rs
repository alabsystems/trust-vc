verus!{
pub struct S<X> { pub x: X }
impl<X> Tr for S<X> { }
impl Q for u8 { }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait U<T> {
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
}
impl<X> U<X> for S<X> {
    open spec fn mm(&self) -> u8 where X: Tr { 2 }
    proof fn lm0(&self) { }
}
pub trait Q { }
} // verus!
