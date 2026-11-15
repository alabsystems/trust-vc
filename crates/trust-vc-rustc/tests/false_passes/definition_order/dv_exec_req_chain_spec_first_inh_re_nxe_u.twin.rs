verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn need(&self) requires self.lim() == 1;
    fn x(&self) -> (r: u8);
    fn y(&self) -> (r: u8);
    fn run(&self) -> (r: u8) ensures r <= 255 { 0 }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { 1 }
    fn x(&self) -> (r: u8) { self.need(); 1 }
    fn need(&self) { }
    fn y(&self) -> (r: u8) { self.x() }
}
fn user() { let v = A { a: 0 }; let r = v.run(); }
} // verus!
