verus!{
pub struct B { pub b: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    proof fn rq0(&self) where T: Tr + Q requires self.mm() == 2;
    proof fn lm1(&self) where T: Tr + Q ensures self.mm() == 2;
}
impl U<A> for B {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
}
impl U<A> for A {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub trait Tr { }
pub struct A { pub a: u8 }
pub trait Q: Tr { }
} // verus!
