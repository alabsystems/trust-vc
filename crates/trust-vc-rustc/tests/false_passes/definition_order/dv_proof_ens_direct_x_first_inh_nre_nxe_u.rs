verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    proof fn x(&self) ensures self.lim() == 1;
    proof fn run(&self) { self.x(); }
}
impl Tr for A {
    proof fn x(&self) {  }
    open spec fn lim(&self) -> u8 { 1 }
}
fn user() { let v = A { a: 0 }; proof { v.run(); } }
} // verus!
