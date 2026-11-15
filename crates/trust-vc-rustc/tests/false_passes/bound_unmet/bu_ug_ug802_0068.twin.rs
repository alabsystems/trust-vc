verus!{
pub trait U<T> {
    proof fn lm1(&self) where T: Tr ensures self.mm() == 2;
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
}
pub struct Z { pub z: u8 }
pub trait Q { }
impl Q for Z { }
pub struct S<X> { pub x: X }
pub trait Tr { }
impl<X: Tr, T: Tr> U<T> for S<X> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm1(&self) where T: Tr { }
    proof fn lm0(&self) { }
}
impl U<u8> for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
} // verus!
