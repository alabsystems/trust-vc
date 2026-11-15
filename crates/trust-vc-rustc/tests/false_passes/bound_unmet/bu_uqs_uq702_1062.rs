verus!{
pub struct Z { pub z: u8 }
impl Tr for Z { }
pub struct A { pub a: u8 }
impl Tr for A { }
impl U<A> for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub trait Q { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
    proof fn lm1(&self) where T: Tr + Q ensures self.mm() == 2;
    proof fn dd(&self) where T: Tr + Q { self.lm1(); }
}
pub struct B { pub b: u8 }
pub trait Tr { }
impl U<A> for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl U<Z> for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
} // verus!
