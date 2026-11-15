verus!{
impl U<A> for A {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
pub trait Q { }
pub struct Z { pub z: u8 }
impl Q for A { }
pub struct B { pub b: u8 }
impl U<Z> for Z {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
impl U<A> for B {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
impl Tr for A { }
pub struct A { pub a: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn rq0(&self) where T: Q requires self.mm() == 2;
    proof fn lm1(&self) where T: Q ensures self.mm() == 2;
}
pub trait Tr { }
} // verus!
