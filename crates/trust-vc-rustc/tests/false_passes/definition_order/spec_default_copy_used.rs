verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    open spec fn dflt(&self) -> u8 { 3 }
    fn x(&self) -> (r: u8) ensures r == self.dflt();
    fn run(&self) -> (r: u8) { self.x() }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { 3 }
}
}
