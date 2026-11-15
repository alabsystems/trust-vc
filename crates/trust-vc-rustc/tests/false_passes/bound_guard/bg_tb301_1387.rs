verus!{
impl Q for A {
    open spec fn q(&self) -> u8 { 5 }
}
pub struct W<X> { pub w: X }
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
impl<X: Tr> Tr for W<X> {
    open spec fn lim(&self) -> u8 { self.w.lim() }
    fn x(&self) -> (r: u8) { self.w.x() }
}
impl U for A {
    proof fn lq(&self) { }
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { 2 }
}
pub trait U: Tr + Q {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    fn dd(&self) { let _r = self.z(); }
    proof fn dlq(&self) { self.lq(); }
    proof fn lq(&self) ensures self.dq() == 4;
    fn z(&self) -> (r: u8) ensures r == self.du();
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub struct A { pub a: u8 }
pub trait Q {
    spec fn q(&self) -> u8;
    open spec fn dq(&self) -> u8 { 4 }
}
} // verus!
