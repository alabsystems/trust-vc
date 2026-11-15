verus!{
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
    proof fn lt(&self) { }
    open spec fn dt(&self) -> u8 { 3 }
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
pub proof fn ut() { let v = A { a: 1 }; assert(v.dt() == 3); }
impl Tr for A {
    proof fn lt(&self) { }
    open spec fn dt(&self) -> u8 { 3 }
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
    proof fn lt(&self) ensures self.dt() == 3;
}
pub struct B { pub b: u8 }
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
impl U for A {
    fn z(&self) -> (r: u8) { 2 }
    open spec fn m(&self) -> u8 { self.a }
}
pub struct A { pub a: u8 }
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
pub trait U: Tr + Q {
    fn z(&self) -> (r: u8) ensures r == self.du();
    open spec fn du(&self) -> u8 { 2 }
    spec fn m(&self) -> u8;
    fn dd(&self) { }
}
} // verus!
