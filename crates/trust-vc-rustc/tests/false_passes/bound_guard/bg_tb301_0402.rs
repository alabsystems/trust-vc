verus!{
pub struct A { pub a: u8 }
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.du();
    fn dd(&self) { let _r = self.z(); }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
    proof fn lt(&self) ensures self.dt() == 3;
    proof fn rl(&self) { self.lt(); }
}
impl U for A {
    fn z(&self) -> (r: u8) { 2 }
    open spec fn m(&self) -> u8 { self.a }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
    proof fn lt(&self) { }
}
} // verus!
