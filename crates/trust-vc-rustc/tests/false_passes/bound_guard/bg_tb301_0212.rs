verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn rx(&self) -> (r: u8) { self.x() }
}
pub trait U: Tr + Q {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.du();
    proof fn lq(&self) ensures self.dq() == 4;
    fn dd(&self) { let _r = self.z(); }
    proof fn dlq(&self) { self.lq(); }
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { 2 }
    proof fn lq(&self) { }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
} // verus!
