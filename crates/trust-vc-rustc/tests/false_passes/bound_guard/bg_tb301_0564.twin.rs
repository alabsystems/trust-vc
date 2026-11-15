verus!{
pub trait U where Self: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.du();
    fn dd(&self) { }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn rx(&self) -> (r: u8) { self.x() }
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub struct A { pub a: u8 }
impl U for A {
    fn z(&self) -> (r: u8) { 2 }
    open spec fn m(&self) -> u8 { self.a }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
} // verus!
