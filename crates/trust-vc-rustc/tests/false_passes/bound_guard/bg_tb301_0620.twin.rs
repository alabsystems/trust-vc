verus!{
pub trait U: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.du();
    fn dd(&self) { }
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { 2 }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    proof fn lt(&self) ensures self.dt() == 3;
    fn rx(&self) -> (r: u8) { self.x() }
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
    proof fn lt(&self) { }
}
pub struct A { pub a: u8 }
} // verus!
