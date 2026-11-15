verus!{
impl U<B> for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub trait Q { }
pub struct Z { pub z: u8 }
impl Q for B { }
pub trait Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
    proof fn lm1(&self) where T: Tr + Q ensures self.mm() == 2;
}
pub struct B { pub b: u8 }
impl U<Z> for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Tr for B { }
} // verus!
