verus!{
impl Tr for B { }
impl U<B> for Z {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn rq1(&self) { }
}
pub trait Q: Tr { }
impl Tr for A { }
pub struct Z { pub z: u8 }
impl Q for A { }
impl Tr for Z { }
pub struct B { pub b: u8 }
pub trait Tr { }
pub struct A { pub a: u8 }
impl U<A> for B {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn rq1(&self) { }
}
pub trait U<T> {
    proof fn rq1(&self) where T: Q requires self.mm() == 2;
    fn z0(&self) -> (r: u8) where T: Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    fn dd(&self) -> (r: u8) where T: Q { self.z0() }
}
impl Q for Z { }
impl U<Z> for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn rq1(&self) { }
}
} // verus!
