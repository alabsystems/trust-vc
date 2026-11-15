verus!{
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    open spec fn dt(&self) -> u8 { 3 }
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn lt(&self) ensures self.dt() == 3;
}
impl Tr for B {
    proof fn lt(&self) { }
    open spec fn dt(&self) -> u8 { 3 }
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
pub struct A { pub a: u8 }
pub trait U: Tr + Q {
    open spec fn du(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.du() == 2;
    proof fn dd(&self) { }
    spec fn m(&self) -> u8;
}
pub struct B { pub b: u8 }
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    proof fn lt(&self) { }
    open spec fn lim(&self) -> u8 { self.a }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
} // verus!
