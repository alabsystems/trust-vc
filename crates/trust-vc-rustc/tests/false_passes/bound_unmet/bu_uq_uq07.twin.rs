verus!{
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait U where Self: Sized {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dl(&self) where Self: Tr { self.lm(); }
}
impl U for Z {
    proof fn lm(&self) { }
}
} // verus!
