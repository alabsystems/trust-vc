verus!{
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where T: Q ensures r == self.mm();
    proof fn lm1(&self) where T: Q ensures self.mm() == 2;
    fn dd(&self) -> (r: u8) where T: Q { self.z0() }
}
pub struct B { pub b: u8 }
impl U<A> for B {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Q { }
impl Tr for A { }
impl Q for A { }
pub struct A { pub a: u8 }
impl Tr for Z { }
pub struct Z { pub z: u8 }
impl U<Z> for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
pub trait Tr { }
} // verus!
