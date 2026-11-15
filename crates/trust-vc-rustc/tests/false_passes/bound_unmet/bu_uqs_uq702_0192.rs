verus!{
pub trait U {
    proof fn rq1(&self) where Self: Q requires self.mm() == 2;
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
}
impl U for Z {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
pub struct B { pub b: u8 }
impl U for A {
    proof fn rq1(&self) { assert(self.mm() == 2); }
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
impl Q for A { }
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait Q { }
} // verus!
