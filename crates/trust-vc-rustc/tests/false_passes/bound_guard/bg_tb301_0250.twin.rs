verus!{
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { 2 }
}
impl Tr for A {
    open spec fn dt(&self) -> u8 { 3 }
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
    proof fn lt(&self) { }
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.du();
    fn dd(&self) { }
}
pub proof fn ut() { let v = A { a: 1 }; assert(v.dt() == 3); }
pub trait Tr {
    proof fn lt(&self) ensures self.dt() == 3;
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
}
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
    proof fn lt(&self) { }
}
} // verus!
