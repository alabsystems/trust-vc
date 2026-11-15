verus!{
pub struct A { pub a: u8 }
pub trait Tr { fn x(&self) -> (r: u8) ensures r == 1; }
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.mm();
    fn dz(&self) -> (r: u8) { self.z() }
}
impl Tr for A { fn x(&self) -> (r: u8) { 1 } }
impl U for A {
    fn z(&self) -> (r: u8) { let k = 1u8; 2 }
}
} // verus!
