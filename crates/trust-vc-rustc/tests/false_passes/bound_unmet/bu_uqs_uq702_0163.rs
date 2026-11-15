verus!{
pub trait Q { }
impl U for A {
    proof fn rq0(&self) { assert(self.mm() == 2); }
    proof fn lm1(&self) { }
}
impl Q for A { }
pub proof fn fA() { (A { a: 0 }).lm1(); }
pub struct B { pub b: u8 }
impl U for B {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn rq0(&self) where Self: Q requires self.mm() == 2;
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
}
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
} // verus!
