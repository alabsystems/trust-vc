verus!{
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
pub struct B { pub b: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn rq0(&self) where Self: Tr + Q requires self.mm() == 2;
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
}
impl U for A {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
} // verus!
