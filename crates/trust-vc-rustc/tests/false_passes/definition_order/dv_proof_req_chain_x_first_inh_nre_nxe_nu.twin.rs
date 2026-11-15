verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    proof fn need(&self) requires self.lim() == 1;
    proof fn x(&self);
    proof fn y(&self);
    proof fn run(&self) { }
}
impl Tr for A {
    proof fn x(&self) { self.need(); }
    open spec fn lim(&self) -> u8 { 1 }
    proof fn need(&self) { }
    proof fn y(&self) { self.x(); }
}
} // verus!
