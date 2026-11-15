verus!{
impl Tr for B { }
impl U for B {
    proof fn rq1(&self) { assert(self.mm() == 2); }
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 } impl Tr for A { } impl Q for A { }
impl U for A {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn rq1(&self) where Self: Tr requires self.mm() == 2;
}
pub trait Q: Tr { }
pub struct A { pub a: u8 }
} // verus!
