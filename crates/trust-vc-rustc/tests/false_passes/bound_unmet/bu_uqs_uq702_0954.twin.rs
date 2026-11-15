verus!{
pub struct B { pub b: u8 } impl Q for Z { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
impl Tr for Z { }
pub trait Q: Tr { }
impl U<Z> for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    proof fn lm1(&self) where T: Q ensures self.mm() == 2;
}
} // verus!
