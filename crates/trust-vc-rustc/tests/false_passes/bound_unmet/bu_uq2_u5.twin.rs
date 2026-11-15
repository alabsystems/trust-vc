verus!{
pub struct Z { pub z: u8 } impl Tr for u8 { }
pub trait Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm(&self) where T: Tr ensures self.mm() == 2;
}
impl U<u8> for Z {
    proof fn lm(&self) { }
}
} // verus!
