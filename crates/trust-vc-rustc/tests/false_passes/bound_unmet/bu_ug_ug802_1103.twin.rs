verus!{
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
pub struct S<X> { pub x: X } impl Tr for Z { }
pub struct Z { pub z: u8 }
impl Q for Z { }
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr { }
}
pub trait Q { }
impl U for Z {
    proof fn lm0(&self) { }
}
pub trait Tr { }
impl<X: Q> Tr for S<X> { }
} // verus!
