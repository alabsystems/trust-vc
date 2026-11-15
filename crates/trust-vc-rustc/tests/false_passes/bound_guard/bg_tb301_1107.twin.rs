verus!{
pub struct B { pub b: u8 }
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
    fn xt(&self) -> (r: u8) { 3 }
}
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn rx(&self) -> (r: u8) { 2 }
    spec fn lim(&self) -> u8;
    open spec fn dt(&self) -> u8 { 3 }
    fn xt(&self) -> (r: u8) ensures r == self.dt();
}
pub trait U: Tr {
    open spec fn du(&self) -> u8 { 2 }
    fn dd(&self) { let _r = self.z(); }
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.du();
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub struct A { pub a: u8 }
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { 2 }
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
impl Tr for B {
    fn xt(&self) -> (r: u8) { 3 }
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
} // verus!
