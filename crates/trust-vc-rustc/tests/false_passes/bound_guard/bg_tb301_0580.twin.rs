verus!{
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
    fn xt(&self) -> (r: u8) { 3 }
}
pub proof fn ut() { let v = A { a: 1 }; assert(v.dt() == 3); }
pub struct A { pub a: u8 }
pub trait U: Tr {
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
    open spec fn du(&self) -> u8 { 2 }
    spec fn m(&self) -> u8;
    proof fn dd(&self) { }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
    fn xt(&self) -> (r: u8) ensures r == self.dt();
}
impl Tr for B {
    fn xt(&self) -> (r: u8) { 3 }
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
}
pub struct B { pub b: u8 }
impl U for B {
    open spec fn m(&self) -> u8 { self.b }
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
}
} // verus!
