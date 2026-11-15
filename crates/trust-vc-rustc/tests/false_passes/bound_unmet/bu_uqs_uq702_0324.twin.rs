verus!{
pub trait U<T> {
    fn z1(&self) -> (r: u8) where T: Tr ensures r == self.mm();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    fn dd(&self) -> (r: u8) where T: Tr { self.z1() }
}
pub proof fn fA() { <A as U<A>>::lm0(&(A { a: 0 })); }
impl U<Z> for B {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
impl U<A> for Z {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
impl Tr for A { }
pub struct Z { pub z: u8 }
impl Q for A { }
impl U<A> for A {
    open spec fn mm(&self) -> u8 { 2 }
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub trait Q { }
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub trait Tr { }
} // verus!
