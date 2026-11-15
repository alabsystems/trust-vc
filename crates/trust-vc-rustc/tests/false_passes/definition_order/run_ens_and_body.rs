verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn run(&self) -> (r: u8) ensures r == self.lim() { let r = self.x(); proof { assert(r == self.lim()); } r }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
fn user() { let v = A { a: 2 }; let r = v.run(); assert(r == 2); }
}
