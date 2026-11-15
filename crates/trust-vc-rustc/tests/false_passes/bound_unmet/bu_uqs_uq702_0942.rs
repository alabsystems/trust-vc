verus!{
impl U<Z> for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Tr for Z { }
pub trait Q { }
impl Tr for A { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
impl U<A> for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct B { pub b: u8 }
pub trait Tr { }
pub trait U<T> {
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    proof fn dd(&self) where T: Q { self.lm0(); }
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm1(&self) where T: Q ensures self.mm() == 2;
}
} // verus!
