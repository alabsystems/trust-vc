verus!{
pub trait Tr { }
pub trait Q { }
impl Q for B { }
pub struct B { pub b: u8 }
impl U<B> for B {
    proof fn lm0(&self) { }
}
impl U<Z> for A {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
}
impl U<Z> for Z {
    proof fn lm0(&self) { }
}
impl Q for Z { }
pub struct Z { pub z: u8 }
} // verus!
