verus!{
impl<X> Tr for S<X> { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
}
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct S<X> { pub x: X }
pub trait Tr { }
impl Tr for u8 { }
pub struct Z { pub z: u8 }
pub trait Q { }
} // verus!
