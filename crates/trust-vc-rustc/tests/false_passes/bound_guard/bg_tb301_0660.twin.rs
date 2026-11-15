verus!{
pub trait U where Self: Tr {
    open spec fn du(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.du();
    spec fn m(&self) -> u8;
    fn dd(&self) { }
}
pub trait Tr {
    open spec fn dt(&self) -> u8 { 3 }
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn xt(&self) -> (r: u8) ensures r == self.dt();
    spec fn lim(&self) -> u8;
}
impl Tr for A {
    fn xt(&self) -> (r: u8) { 3 }
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub struct A { pub a: u8 }
impl U for A {
    fn z(&self) -> (r: u8) { 2 }
    open spec fn m(&self) -> u8 { self.a }
}
} // verus!
