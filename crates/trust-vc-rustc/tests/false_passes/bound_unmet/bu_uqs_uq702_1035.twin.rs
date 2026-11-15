verus!{
pub trait Q { }
impl Tr for Z { }
impl U<B> for B {
    proof fn lm0(&self) { }
}
impl U<Z> for Z {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
impl Tr for A { }
pub trait Tr { }
pub struct B { pub b: u8 }
impl U<A> for A {
    proof fn lm0(&self) { }
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
    proof fn dd(&self) where T: Tr + Q { self.lm0(); }
}
pub struct Z { pub z: u8 }
} // verus!
