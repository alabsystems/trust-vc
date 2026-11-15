verus!{
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
impl U for Z {
    fn z(&self) -> (r: u8) { 2 }
}
} // verus!
