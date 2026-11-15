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
    fn z(&self) -> (r: u8) ensures r == self.mm();
    fn dm(&self) { let _r = self.z(); }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { 7 }
}
impl Q for A {
    open spec fn q(&self) -> u8 { 8 }
}
impl U for A {
    fn z(&self) -> (r: u8) { 2 }
}
} // verus!
