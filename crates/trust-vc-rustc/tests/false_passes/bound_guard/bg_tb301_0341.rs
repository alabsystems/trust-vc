verus!{
pub struct A { pub a: u8 }
pub struct W<X> { pub w: X }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub fn uw() { let v = W { w: A { a: 6 } }; let r = v.x(); assert(r == 6); }
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub trait U where Self: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    proof fn need(&self) requires self.du() == 2;
    proof fn lm(&self);
    proof fn dd(&self) { self.lm(); }
}
impl<X: Tr> Tr for W<X> {
    fn x(&self) -> (r: u8) { self.w.x() }
    open spec fn lim(&self) -> u8 { self.w.lim() }
}
} // verus!
