verus!{
pub struct A { pub a: u8 }
pub trait Tr { }
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { }
}
impl Tr for A { }
impl U for A {
    proof fn lm(&self) { }
}
pub proof fn q() where A: Tr { assert((A { a: 1 }).mm() == 2); }
} // verus!
