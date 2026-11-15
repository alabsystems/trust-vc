verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    spec fn other(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl Tr for A {
    fn x(&self) -> (r: u8) ensures r == self.lim() { self.a }
    open spec fn lim(&self) -> u8 { self.a }
    open spec fn other(&self) -> u8 { 0 }
}
pub mod m {
    use super::*;
    pub open spec fn s() -> u8 { (A { a: 1 }).other() }
}
}
