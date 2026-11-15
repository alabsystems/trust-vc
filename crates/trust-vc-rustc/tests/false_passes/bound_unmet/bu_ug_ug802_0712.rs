verus!{
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
impl U<u8> for Z {
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub trait Q { }
impl Q for Z { }
impl<X: Tr> U<X> for S<X> {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
}
impl<X> Tr for S<X> { }
impl Q for u8 { }
} // verus!
