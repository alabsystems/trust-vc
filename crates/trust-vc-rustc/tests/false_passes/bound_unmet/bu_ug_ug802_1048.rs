verus!{
pub struct S<X> { pub x: X }
impl Q for u8 { }
impl<T> U<T> for Z {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
}
pub struct Z { pub z: u8 }
impl<X> Tr for S<X> { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
}
pub trait Tr { }
pub trait Q { }
} // verus!
