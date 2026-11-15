verus!{
impl Tr for A {
    proof fn lt(&self) { }
    open spec fn dt(&self) -> u8 { 3 }
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
    proof fn lt(&self) ensures self.dt() == 3;
}
pub struct A { pub a: u8 }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { 2 }
}
pub trait U where Self: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.du();
    fn dd(&self) { }
}
} // verus!
