verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn need(&self) requires self.lim() == 1;
    fn x(&self);
    fn run(&self) { }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { 1 }
    fn need(&self) { }
    fn x(&self) { self.need() }
}
}
