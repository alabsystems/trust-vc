verus!{
pub struct A { pub a: u8 }
impl U<A> for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
impl Q for B { }
impl Tr for B { }
impl U<Z> for Z {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
impl U<B> for B {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
impl Tr for A { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where T: Q ensures r == self.mm();
}
pub trait Q: Tr { }
} // verus!
