verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    open spec fn s(&self) -> bool { true }
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn run(&self) -> (r: u8) { self.x() }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
}
