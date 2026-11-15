verus!{
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
    proof fn lt(&self) ensures self.dt() == 3;
    proof fn rl(&self) { }
}
impl U for B {
    fn z(&self) -> (r: u8) { 2 }
    open spec fn m(&self) -> u8 { self.b }
    proof fn lq(&self) { }
}
pub struct B { pub b: u8 }
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
    open spec fn dt(&self) -> u8 { 3 }
    proof fn lt(&self) { }
}
impl Tr for A {
    proof fn lt(&self) { }
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
    open spec fn dt(&self) -> u8 { 3 }
}
pub struct A { pub a: u8 }
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait U: Tr + Q {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    fn dd(&self) { let _r = self.z(); }
    fn z(&self) -> (r: u8) ensures r == self.du();
    proof fn dlq(&self) { self.lq(); }
    proof fn lq(&self) ensures self.dq() == 4;
}
impl U for A {
    proof fn lq(&self) { }
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { 2 }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
} // verus!
