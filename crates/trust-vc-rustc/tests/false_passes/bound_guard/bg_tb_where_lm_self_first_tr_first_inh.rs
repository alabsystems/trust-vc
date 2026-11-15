verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
}
pub trait U where Self: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { self.lm(); }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { 7 }
}
impl U for A {
    proof fn lm(&self) { }
}
} // verus!
