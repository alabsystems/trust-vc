verus!{
pub trait U: Tr {
    fn z(&self) -> (r: u8) ensures r == self.du();
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    fn dd(&self) { }
}
impl U for B {
    fn z(&self) -> (r: u8) { 2 }
    open spec fn m(&self) -> u8 { self.b }
}
pub struct B { pub b: u8 }
pub trait Tr {
    fn xt(&self) -> (r: u8) ensures r == self.dt();
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
}
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
impl Tr for B {
    fn xt(&self) -> (r: u8) { 3 }
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { 2 }
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
    fn xt(&self) -> (r: u8) { 3 }
}
pub struct A { pub a: u8 }
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
} // verus!
