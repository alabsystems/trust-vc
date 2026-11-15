verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn lim_e(&self) -> (r: u8) ensures r == self.lim();
    fn run(&self) -> (r: u8) { self.lim_e() }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn lim_e(&self) -> (r: u8) { self.a }
}
fn user() { let r = (A { a: 4 }).run(); let q = (A { a: 4 }).lim_e(); assert(q == 4); }
}
