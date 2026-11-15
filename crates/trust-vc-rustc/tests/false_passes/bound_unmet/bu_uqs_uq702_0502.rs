verus!{
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn rq1(&self) where Self: Tr requires self.mm() == 2;
}
pub struct Z { pub z: u8 }
pub trait Tr { }
impl Q for A { }
pub trait Q { }
pub struct B { pub b: u8 }
impl U for A {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
pub struct A { pub a: u8 }
} // verus!
