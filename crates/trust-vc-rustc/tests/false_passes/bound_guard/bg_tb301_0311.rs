verus!{
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    proof fn lt(&self) { }
    open spec fn lim(&self) -> u8 { self.b }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    open spec fn dt(&self) -> u8 { 3 }
    proof fn lt(&self) ensures self.dt() == 3;
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
impl Q for B {
    open spec fn q(&self) -> u8 { 5 }
}
impl U for A {
    proof fn lq(&self) { }
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
    open spec fn du(&self) -> u8 { 2 }
    open spec fn m(&self) -> u8 { self.a }
}
impl U for B {
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
    open spec fn m(&self) -> u8 { self.b }
    proof fn lq(&self) { }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
    proof fn lt(&self) { }
}
pub proof fn uu() { let v = A { a: 1 }; v.lm(); }
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
pub trait U: Tr + Q {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
    proof fn lq(&self) ensures self.dq() == 4;
    proof fn dd(&self) { self.lm(); }
    proof fn dlq(&self) { self.lq(); }
}
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
pub proof fn ut() { let v = A { a: 1 }; assert(v.dt() == 3); }
} // verus!
