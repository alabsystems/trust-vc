verus!{
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
impl<X: Q> Tr for S<X> { }
pub trait Tr { }
impl Q for Z { }
impl Tr for u8 { }
impl U for Z {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
pub trait Q { }
impl<X> U for S<X> {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
} // verus!
