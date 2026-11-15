verus!{
pub trait Q { } impl Tr for Z { } impl Q for Z { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
pub struct S<X> { pub x: X }
pub trait Tr { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) { }
}
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
impl<X> Tr for S<X> { }
} // verus!
