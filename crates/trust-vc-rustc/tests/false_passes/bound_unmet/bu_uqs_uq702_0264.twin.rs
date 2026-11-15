verus!{
pub trait Tr { }
impl U<A> for A {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
impl U<Z> for B {
    proof fn lm0(&self) { }
}
impl Tr for Z { }
pub trait Q { }
pub struct B { pub b: u8 }
impl Q for Z { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub trait U<T> {
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
}
impl U<A> for Z {
    proof fn lm0(&self) { }
}
} // verus!
