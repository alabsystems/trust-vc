verus!{
impl Tr for Z { }
impl U<A> for B {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub trait U<T> {
    proof fn dd(&self) where T: Tr + Q { self.lm0(); }
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where T: Tr + Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Q { }
pub proof fn fA() { <A as U<B>>::lm0(&(A { a: 0 })); }
pub struct B { pub b: u8 }
impl U<B> for A {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
impl U<Z> for Z {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
impl Tr for B { }
impl Q for B { }
} // verus!
