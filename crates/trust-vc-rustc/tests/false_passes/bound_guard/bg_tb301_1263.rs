verus!{
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    fn xt(&self) -> (r: u8) { 3 }
    open spec fn lim(&self) -> u8 { self.a }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
    fn xt(&self) -> (r: u8) ensures r == self.dt();
    fn rx(&self) -> (r: u8) { self.x() }
}
impl U for A {
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
    open spec fn m(&self) -> u8 { self.a }
}
pub proof fn ut() { let v = A { a: 1 }; assert(v.dt() == 3); }
pub struct A { pub a: u8 }
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
    fn xt(&self) -> (r: u8) { 3 }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
impl U for B {
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
    open spec fn m(&self) -> u8 { self.b }
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait U: Tr + Q {
    open spec fn du(&self) -> u8 { 2 }
    proof fn dd(&self) { self.lm(); }
    spec fn m(&self) -> u8;
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
}
pub struct B { pub b: u8 }
} // verus!
