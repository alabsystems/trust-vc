verus!{
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
    proof fn rq1(&self) where T: Tr + Q requires self.mm() == 2;
}
pub struct B { pub b: u8 }
pub trait Q { }
impl U<B> for A {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
impl Q for B { }
pub proof fn fB() { <B as U<Z>>::lm0(&(B { b: 0 })); }
pub trait Tr { }
impl Q for Z { }
impl U<Z> for B {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
impl Tr for Z { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
impl U<B> for Z {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
} // verus!
