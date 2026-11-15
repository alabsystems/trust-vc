verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn lim_e(&self) -> (r: u8) ensures r == self.lim();
    fn run(&self) -> (r: u8) { 0 }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn lim_e(&self) -> (r: u8) { self.a }
}
impl Tr for u8 {
    open spec fn lim(&self) -> u8 { *self }
    fn lim_e(&self) -> (r: u8) { *self }
}
}
