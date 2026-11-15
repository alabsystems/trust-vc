verus!{
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
impl<T: Tr> U<T> for Z {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr { }
    proof fn lm1(&self) { }
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where T: Tr ensures self.mm() == 2;
}
impl Q for u8 { }
pub trait Tr { }
impl Tr for Z { }
impl Tr for u8 { }
pub trait Q { }
impl Q for Z { }
} // verus!
