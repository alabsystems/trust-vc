verus!{
pub struct A { pub a: u8 }
pub trait Tr { }
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.mm();
    fn dz(&self) -> (r: u8) { 2 }
}
impl Tr for A { }
impl U for A {
    fn z(&self) -> (r: u8) { 2 }
}
} // verus!
