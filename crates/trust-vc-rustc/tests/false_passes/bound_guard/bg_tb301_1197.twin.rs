verus!{
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
    fn xt(&self) -> (r: u8) ensures r == self.dt();
}
pub trait U where Self: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.du() == 2;
    proof fn dd(&self) { }
}
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
pub struct B { pub b: u8 }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn xt(&self) -> (r: u8) { 3 }
    open spec fn dt(&self) -> u8 { 3 }
    fn x(&self) -> (r: u8) { self.b }
}
pub proof fn ut() { let v = A { a: 1 }; assert(v.dt() == 3); }
impl U for B {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.b }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
    fn xt(&self) -> (r: u8) { 3 }
}
pub struct A { pub a: u8 }
} // verus!
