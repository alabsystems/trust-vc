verus!{
pub trait Tr { spec fn lim(&self) -> u8; }
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { self.lm(); }
}
pub struct A { pub a: u8 }
impl Tr for A { open spec fn lim(&self) -> u8 { 7 } }
impl U for A {
    proof fn lm(&self) { }
}
} // verus!
