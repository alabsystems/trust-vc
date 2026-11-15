verus!{
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub struct B { pub b: u8 }
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
impl U for B {
    fn z(&self) -> (r: u8) { 2 }
    open spec fn m(&self) -> u8 { self.b }
}
pub struct A { pub a: u8 }
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub trait U where Self: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.du();
    fn dd(&self) { let _r = self.z(); }
}
impl U for A {
    fn z(&self) -> (r: u8) { 2 }
    open spec fn m(&self) -> u8 { self.a }
}
} // verus!
