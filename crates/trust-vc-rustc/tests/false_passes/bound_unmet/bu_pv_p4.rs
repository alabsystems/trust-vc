verus!{
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm(&self) where T: Tr ensures self.mm() == 2;
}
impl<T> U<T> for Z {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm(&self) { }
}
} // verus!
