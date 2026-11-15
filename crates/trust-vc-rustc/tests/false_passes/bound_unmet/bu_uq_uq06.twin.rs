verus!{
pub struct Z { pub z: u8 } impl Q for Z { }
pub trait Tr { }
pub trait Q { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm(&self) where Self: Tr + Q ensures self.mm() == 2;
}
impl Tr for Z { }
impl U for Z {
    proof fn lm(&self) { }
}
} // verus!
