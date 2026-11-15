verus!{
pub struct Z { pub z: u8 }
pub trait Tr<T> { }
impl Tr<u8> for Z { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr<u8> { 2 }
    proof fn lm(&self) where Self: Tr<u8> ensures self.mm() == 2;
}
impl U for Z {
    proof fn lm(&self) { }
}
} // verus!
