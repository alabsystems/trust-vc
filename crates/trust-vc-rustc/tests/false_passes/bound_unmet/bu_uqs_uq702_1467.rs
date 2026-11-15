verus!{
pub trait U<T> {
    proof fn rq1(&self) where T: Tr requires self.mm() == 2;
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
}
pub struct A { pub a: u8 }
pub trait Q { }
pub struct B { pub b: u8 }
impl U<A> for A {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
pub trait Tr { }
pub struct Z { pub z: u8 }
} // verus!
