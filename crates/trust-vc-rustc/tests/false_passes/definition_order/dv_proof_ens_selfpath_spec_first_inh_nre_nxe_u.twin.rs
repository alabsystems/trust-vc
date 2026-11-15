verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    proof fn x(&self) ensures self.lim() == 1;
    proof fn run(&self) { Self::x(self); }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { 1 }
    proof fn x(&self) ensures self.lim() == 1 {  }
}
fn user() { let v = A { a: 0 }; proof { v.run(); } }
} // verus!
