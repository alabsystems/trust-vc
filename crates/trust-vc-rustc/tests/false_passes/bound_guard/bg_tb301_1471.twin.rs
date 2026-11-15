verus!{
impl U for A {
    fn z(&self) -> (r: u8) { 2 }
    open spec fn m(&self) -> u8 { self.a }
}
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn rx(&self) -> (r: u8) { self.x() }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub trait U: Tr {
    open spec fn du(&self) -> u8 { 2 }
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.du();
    fn dd(&self) { }
}
pub fn uu() { let v = A { a: 1 }; let r = v.z(); assert(r == 2 || r == 1); }
} // verus!
