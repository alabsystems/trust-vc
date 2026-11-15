verus!{
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
impl Q for Z { } impl Tr for Z { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm(&self) where Self: Tr + Q ensures self.mm() == 2;
}
impl U for Z {
    proof fn lm(&self) { }
}
} // verus!
