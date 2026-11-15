verus!{
impl U<A> for B {
    fn z0(&self) -> (r: u8) { 2 }
}
pub fn fZ() { let _r = <Z as U<B>>::z0(&(Z { z: 0 })); }
impl Tr for A { }
impl Q for A { }
pub struct Z { pub z: u8 }
pub fn fB() { let _r = <B as U<A>>::z0(&(B { b: 0 })); }
impl U<Z> for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct A { pub a: u8 }
impl U<B> for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Q { }
pub struct B { pub b: u8 }
impl Tr for B { }
pub trait Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
    fn dd(&self) -> (r: u8) where T: Tr { self.z0() }
}
} // verus!
