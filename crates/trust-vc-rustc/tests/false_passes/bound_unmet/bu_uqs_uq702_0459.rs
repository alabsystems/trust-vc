verus!{
pub struct Z { pub z: u8 }
impl Tr for Z { }
impl Q for Z { }
pub proof fn fB() { <B as U<Z>>::lm0(&(B { b: 0 })); }
pub struct B { pub b: u8 }
pub trait Q: Tr { }
pub struct A { pub a: u8 }
impl U<A> for Z {
    proof fn lm0(&self) { }
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
    proof fn dd(&self) where T: Tr + Q { self.lm0(); }
}
impl U<Z> for B {
    proof fn lm0(&self) { }
}
pub trait Tr { }
impl U<B> for A {
    proof fn lm0(&self) { }
}
} // verus!
