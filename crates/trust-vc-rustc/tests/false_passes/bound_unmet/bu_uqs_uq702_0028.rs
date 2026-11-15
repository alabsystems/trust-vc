verus!{
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait U<T> {
    proof fn rq0(&self) where T: Q requires self.mm() == 2;
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn dd(&self) where T: Q { self.lm1(); }
    proof fn lm1(&self) where T: Q ensures self.mm() == 2;
}
impl Q for A { }
pub struct A { pub a: u8 }
impl U<A> for A {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { assert(self.mm() == 2); }
}
pub struct B { pub b: u8 }
pub trait Q { }
impl U<Z> for B {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
}
} // verus!
