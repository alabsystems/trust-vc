verus!{
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl U for A {
    fn z(&self) -> (r: u8) { 2 }
    open spec fn m(&self) -> u8 { self.a }
}
pub struct A { pub a: u8 }
pub trait U: Tr {
    fn z(&self) -> (r: u8) ensures r == self.du();
    open spec fn du(&self) -> u8 { 2 }
    fn dd(&self) { }
    spec fn m(&self) -> u8;
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
} // verus!
