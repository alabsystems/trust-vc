verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
}
pub trait Q {
    spec fn q(&self) -> u8;
}
pub trait U: Tr + Q {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { }
}
impl U for A {
    proof fn lm(&self) { }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { 7 }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 8 }
}
} // verus!
