verus!{
impl U<B> for Z {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    fn z0(&self) -> (r: u8) where T: Q ensures r == self.mm();
    proof fn lm1(&self) where T: Q ensures self.mm() == 2;
    fn dd(&self) -> (r: u8) where T: Q { self.z0() }
}
pub struct B { pub b: u8 }
pub proof fn fA() { <A as U<Z>>::lm1(&(A { a: 0 })); }
pub struct Z { pub z: u8 }
pub trait Tr { }
impl Tr for Z { }
impl U<Z> for A {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
impl Q for Z { }
pub trait Q: Tr { }
impl U<Z> for B {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct A { pub a: u8 }
} // verus!
