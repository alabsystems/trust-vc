verus!{
impl<X: Q> Tr for S<X> { }
pub trait Q { } impl Tr for u8 { } impl Q for u8 { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
}
impl Q for Z { }
pub struct Z { pub z: u8 }
impl U<u8> for Z {
    proof fn lm0(&self) { }
}
pub struct S<X> { pub x: X }
pub trait Tr { }
impl Tr for Z { }
} // verus!
