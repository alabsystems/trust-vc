verus!{
pub struct A { pub a: u8 }
pub trait Tr { }
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { self.lm(); }
}
impl U for A {
    proof fn lm(&self) { }
}
pub mod m { use super::*; impl Tr for A { } }
} // verus!
