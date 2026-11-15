verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    proof fn l(&self) ensures self.lim() == 1;
    proof fn run(&self) { self.l(); }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { 1 }
    proof fn l(&self) { }
}
proof fn user() { A { a: 0 }.l(); assert(A { a: 0 }.lim() == 1); }
}
