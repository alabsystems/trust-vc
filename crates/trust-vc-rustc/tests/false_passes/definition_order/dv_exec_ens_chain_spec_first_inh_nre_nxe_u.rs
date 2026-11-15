verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn y(&self) -> (r: u8);
    fn run(&self) -> (r: u8) { self.y() }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { 1 }
    fn x(&self) -> (r: u8) { 1 }
    fn y(&self) -> (r: u8) { self.x() }
}
fn user() { let v = A { a: 0 }; let r = v.run(); }
} // verus!
