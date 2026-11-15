verus!{
pub struct Z { pub z: u8 } impl Q for Z { }
pub trait Tr { }
pub trait Q { }
impl<X: Q> Tr for X { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm(&self) where Self: Tr ensures self.mm() == 2;
}
impl U for Z {
    proof fn lm(&self) { }
}
} // verus!
