verus!{
pub struct Z9 { pub z9: u8 }
pub struct A { pub a: u8 }
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    fn dz(&self) -> (r: u8) where Self: Tr { 2 }
}
impl Tr for A { }
impl U for A {
    fn z(&self) -> (r: u8) { 2 }
}
impl U for Z9 {
    fn z(&self) -> (r: u8) { 2 }
}
} // verus!
