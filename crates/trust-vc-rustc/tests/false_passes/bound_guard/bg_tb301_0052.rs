verus!{
pub struct A { pub a: u8 }
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
pub struct B { pub b: u8 }
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
}
pub trait U: Tr {
    open spec fn du(&self) -> u8 { 2 }
    proof fn dd(&self) { self.lm(); }
    spec fn m(&self) -> u8;
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
}
pub proof fn ut() { let v = A { a: 1 }; assert(v.dt() == 3); }
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    proof fn lt(&self) { }
    fn x(&self) -> (r: u8) { self.a }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn rx(&self) -> (r: u8) { self.x() }
    proof fn lt(&self) ensures self.dt() == 3;
    open spec fn dt(&self) -> u8 { 3 }
}
impl Tr for B {
    proof fn lt(&self) { }
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
} // verus!
