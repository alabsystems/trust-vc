verus!{
pub struct A { pub a: u8 }
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub struct B { pub b: u8 }
impl U for B {
    open spec fn m(&self) -> u8 { self.b }
    fn z(&self) -> (r: u8) { 2 }
}
pub trait U: Tr + Q {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.du();
    fn dd(&self) { let _r = self.z(); }
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { 2 }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub fn uu() { let v = A { a: 1 }; let r = v.z(); assert(r == 2 || r == 1); }
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
} // verus!
