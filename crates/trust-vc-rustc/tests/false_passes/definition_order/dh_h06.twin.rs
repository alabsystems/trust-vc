verus!{
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn lim_e(&self) -> (r: u8) ensures r == self.lim();
    fn run(&self) -> u8 { 0 }
}
pub struct A { pub a: u8 }
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn lim_e(&self) -> (r: u8) { self.a }
}
fn user() { let v = A { a: 2 }; let r = v.run(); }
}
