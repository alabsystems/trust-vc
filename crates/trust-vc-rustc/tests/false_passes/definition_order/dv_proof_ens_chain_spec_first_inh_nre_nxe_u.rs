verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    proof fn x(&self) ensures self.lim() == 1;
    proof fn y(&self);
    proof fn run(&self) { self.y(); }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { 1 }
    proof fn x(&self) {  }
    proof fn y(&self) { self.x(); }
}
fn user() { let v = A { a: 0 }; proof { v.run(); } }
} // verus!
