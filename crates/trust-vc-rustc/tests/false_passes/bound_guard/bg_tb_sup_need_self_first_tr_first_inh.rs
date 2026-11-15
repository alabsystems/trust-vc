verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
}
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn need(&self) requires self.mm() == 2;
    proof fn lm(&self);
    proof fn dm(&self) { self.lm(); }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { 7 }
}
impl U for A {
    proof fn need(&self) { }
    proof fn lm(&self) { self.need(); }
}
} // verus!
