verus!{
pub struct Z { pub z: u8 }
pub trait Tr { } impl Tr for Z { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    open spec fn nn(&self) -> u8 where Self: Tr { self.mm() }
    proof fn lm(&self) where Self: Tr ensures self.nn() == 2;
}
impl U for Z {
    proof fn lm(&self) { }
}
} // verus!
