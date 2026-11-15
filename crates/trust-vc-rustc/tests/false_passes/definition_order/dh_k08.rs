verus!{
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn lim_e(&self) -> (r: u8) ensures r == self.lim();
    fn run(&self) -> (r: u8) { self.lim_e() }
}
pub struct A { pub a: u8 }
pub struct B;
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn lim_e(&self) -> (r: u8) { self.a }
}
impl Tr for B {
    open spec fn lim(&self) -> u8 { 7 }
    fn lim_e(&self) -> (r: u8) { 7 }
}
}
