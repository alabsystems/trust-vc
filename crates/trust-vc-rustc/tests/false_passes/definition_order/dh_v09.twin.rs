verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    fn run(&self) -> (r: u8) { 0 }
    spec fn lim(&self) -> u8;
    fn lim_e(&self) -> (r: u8) ensures r == self.lim();
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn lim_e(&self) -> (r: u8) { self.a }
}
}
