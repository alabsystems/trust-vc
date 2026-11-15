verus!{
pub trait Tr {
    spec fn lim(&self) -> u8;
    proof fn lp(&self) ensures self.lim() == 3;
    proof fn run(&self) { self.lp(); }
}
pub struct A;
impl Tr for A {
    open spec fn lim(&self) -> u8 { 3 }
    proof fn lp(&self) ensures self.lim() == 3 { }
}
}
