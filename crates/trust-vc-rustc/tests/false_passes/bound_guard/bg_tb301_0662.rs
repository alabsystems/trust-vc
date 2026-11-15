verus!{
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { 2 }
}
pub trait U: Tr + Q {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.du();
    fn dd(&self) { let _r = self.z(); }
}
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    proof fn lt(&self) { }
    fn x(&self) -> (r: u8) { self.b }
}
impl U for B {
    fn z(&self) -> (r: u8) { 2 }
    open spec fn m(&self) -> u8 { self.b }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
    spec fn lim(&self) -> u8;
    proof fn lt(&self) ensures self.dt() == 3;
}
pub fn uu() { let v = A { a: 1 }; let r = v.z(); assert(r == 2 || r == 1); }
pub struct A { pub a: u8 }
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub struct B { pub b: u8 }
impl Tr for A {
    open spec fn dt(&self) -> u8 { 3 }
    proof fn lt(&self) { }
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
} // verus!
