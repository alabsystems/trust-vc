verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn run(&self) -> (r: u8) { Self::x(self) }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { 1 }
    open spec fn lim(&self) -> u8 { 1 }
}
} // verus!
