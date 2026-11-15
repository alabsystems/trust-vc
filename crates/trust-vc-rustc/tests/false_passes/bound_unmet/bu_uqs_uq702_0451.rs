verus!{
impl U<Z> for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct Z { pub z: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn dd(&self) where T: Tr { self.lm1(); }
    proof fn lm1(&self) where T: Tr ensures self.mm() == 2;
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
}
pub proof fn fB() { <B as U<B>>::lm0(&(B { b: 0 })); }
pub trait Q { }
impl U<B> for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub trait Tr { }
pub struct A { pub a: u8 }
impl U<B> for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct B { pub b: u8 }
impl Tr for B { }
impl Q for Z { }
} // verus!
