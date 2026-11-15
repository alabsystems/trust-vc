verus!{
pub struct B { pub b: u8 }
pub trait Tr { }
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { self.lm(); }
}
impl U for B {
    proof fn lm(&self) { }
}
impl Tr for B { }
} // verus!
