verus!{
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { 2 }
}
pub struct A { pub a: u8 }
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn rx(&self) -> (r: u8) { self.x() }
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub trait U: Tr + Q {
    fn z(&self) -> (r: u8) ensures r == self.du();
    open spec fn du(&self) -> u8 { 2 }
    fn dd(&self) { let _r = self.z(); }
    spec fn m(&self) -> u8;
}
impl<X: Tr> Tr for W<X> {
    fn x(&self) -> (r: u8) { self.w.x() }
    open spec fn lim(&self) -> u8 { self.w.lim() }
}
pub struct W<X> { pub w: X }
pub proof fn pu() { let v = A { a: 1 }; assert(v.du() == 2); }
pub fn uu() { let v = A { a: 1 }; let r = v.z(); assert(r == 2 || r == 1); }
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
} // verus!
