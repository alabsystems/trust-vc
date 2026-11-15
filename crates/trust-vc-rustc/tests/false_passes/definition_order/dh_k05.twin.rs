verus!{
pub trait Tr {
    spec fn lim(&self) -> u8;
    proof fn l(&self) ensures self.lim() > 0;
    fn run(&self) { proof { self.l(); } }
}
pub struct A { pub a: u8 }
impl Tr for A {
    open spec fn lim(&self) -> u8 { 1 }
    proof fn l(&self) ensures self.lim() > 0 { }
}
}
