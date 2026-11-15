verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn run(&self) -> u8 { self.x() }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { 1 }
    open spec fn lim(&self) -> u8 { 1 }
}
}
