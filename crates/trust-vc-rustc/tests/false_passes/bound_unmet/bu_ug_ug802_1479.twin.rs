verus!{
pub struct S<X> { pub x: X } impl Tr for Z { } impl Q for Z { }
pub struct Z { pub z: u8 }
pub trait Tr { }
impl<X> Tr for S<X> { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
impl U for Z {
    proof fn lm0(&self) { }
}
pub trait Q { }
} // verus!
