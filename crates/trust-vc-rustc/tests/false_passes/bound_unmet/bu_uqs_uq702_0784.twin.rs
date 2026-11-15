verus!{
pub struct Z { pub z: u8 }
pub trait Q: Tr { }
impl U<B> for A {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
}
impl Tr for Z { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn rq0(&self) where T: Q requires self.mm() == 2;
    proof fn lm1(&self) where T: Q ensures self.mm() == 2;
    proof fn dd(&self) where T: Q { self.lm1(); }
}
pub struct B { pub b: u8 }
impl Tr for B { }
pub trait Tr { }
pub struct A { pub a: u8 }
impl Q for B { }
impl U<Z> for B {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
} // verus!
