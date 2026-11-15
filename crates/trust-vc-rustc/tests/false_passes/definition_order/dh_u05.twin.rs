verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn run2(&self) -> (r: u8) { 0 }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { 1 }
    fn x(&self) -> (r: u8) { 1 }
    fn run2(&self) -> (r: u8) { 1 }
}
pub struct B;
impl Tr for B {
    open spec fn lim(&self) -> u8 { 1 }
    fn x(&self) -> (r: u8) { 1 }
}
}
