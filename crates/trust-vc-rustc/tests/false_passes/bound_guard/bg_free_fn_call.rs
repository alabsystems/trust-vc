verus!{
pub struct A { pub a: u8 }
pub trait Tr { }
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8);
    fn dz(&self) -> (r: u8) { self.z() }
}
impl Tr for A { }
impl U for A {
    fn z(&self) -> (r: u8) { 2 }
}
pub fn f(a: &A) -> (r: u8) ensures r == a.mm() { 2 }
} // verus!
