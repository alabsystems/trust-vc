verus!{
pub proof fn fB() { <B as U<B>>::lm0(&(B { b: 0 })); }
impl U<B> for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Tr for B { }
impl Q for A { }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
impl U<B> for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct B { pub b: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where T: Tr ensures self.mm() == 2;
}
pub trait Q { }
pub trait Tr { }
impl U<A> for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
} // verus!
