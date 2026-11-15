verus!{
impl Q for Z { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where T: Tr ensures self.mm() == 2;
}
pub trait Q { }
pub struct S<X> { pub x: X }
impl<X> Tr for S<X> { }
impl<X: Tr, T: Tr> U<T> for S<X> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub trait Tr { }
impl Q for u8 { }
impl Tr for Z { }
pub struct Z { pub z: u8 }
} // verus!
