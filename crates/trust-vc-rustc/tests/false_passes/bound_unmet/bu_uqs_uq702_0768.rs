verus!{
impl U<A> for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    fn z0(&self) -> (r: u8) where T: Q ensures r == self.mm();
}
pub struct B { pub b: u8 }
pub trait Tr { }
impl U<B> for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct A { pub a: u8 }
pub trait Q { }
pub struct Z { pub z: u8 }
impl Q for B { }
pub fn fA() { let _r = <A as U<B>>::z0(&(A { a: 0 })); }
impl Tr for A { }
} // verus!
