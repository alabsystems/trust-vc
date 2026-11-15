verus!{
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm(&self) where Self: Tr ensures self.mm() == 2;
}
impl U for Z {
    proof fn lm(&self) { }
}
} // verus!
