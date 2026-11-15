verus!{
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    proof fn lt(&self) { }
    open spec fn lim(&self) -> u8 { self.b }
}
pub trait Tr {
    open spec fn dt(&self) -> u8 { 3 }
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn rl(&self) { }
    proof fn lt(&self) ensures self.dt() == 3;
    spec fn lim(&self) -> u8;
}
pub struct B { pub b: u8 }
impl Tr for A {
    open spec fn dt(&self) -> u8 { 3 }
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
    proof fn lt(&self) { }
}
impl U for B {
    fn z(&self) -> (r: u8) { 2 }
    open spec fn m(&self) -> u8 { self.b }
}
pub struct A { pub a: u8 }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { 2 }
}
pub trait U: Tr {
    open spec fn du(&self) -> u8 { 2 }
    fn dd(&self) { let _r = self.z(); }
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.du();
}
} // verus!
