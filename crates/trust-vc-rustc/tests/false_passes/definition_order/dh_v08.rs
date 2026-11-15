verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn lim_e(&self) -> (r: u8) ensures r == self.lim();
    fn run(&self) -> (r: u8) { self.lim_e() }
}
impl Tr for A {
    fn lim_e(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
}
