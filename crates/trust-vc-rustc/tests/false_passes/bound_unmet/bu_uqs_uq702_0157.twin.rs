verus!{
impl U<Z> for Z {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
}
impl U<A> for A {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct B { pub b: u8 }
impl U<B> for B {
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub trait Q { }
pub struct Z { pub z: u8 }
} // verus!
