verus!{
pub struct A { pub a: u8 }
impl Tr for Z { }
impl U<Z> for Z {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
impl U<A> for A {
    proof fn lm0(&self) { }
}
pub trait Q { }
pub trait Tr { }
pub struct B { pub b: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
}
impl U<Z> for B {
    proof fn lm0(&self) { }
}
impl Q for Z { }
} // verus!
