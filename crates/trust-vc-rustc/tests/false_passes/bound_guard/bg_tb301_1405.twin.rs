verus!{
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    open spec fn du(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.du();
    fn dd(&self) { }
}
pub fn uu() { let v = A { a: 1 }; let r = v.z(); assert(r == 2 || r == 1); }
pub struct A { pub a: u8 }
impl U for A {
    fn z(&self) -> (r: u8) { 2 }
    open spec fn m(&self) -> u8 { self.a }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
} // verus!
