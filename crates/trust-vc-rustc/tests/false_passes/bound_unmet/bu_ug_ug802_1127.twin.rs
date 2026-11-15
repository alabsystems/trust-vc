verus!{
pub struct S<X> { pub x: X }
pub trait Tr { }
pub trait Q { }
impl Tr for Z { }
impl<X: Q> Tr for S<X> { }
pub struct Z { pub z: u8 }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) { }
}
impl Q for Z { }
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
} // verus!
