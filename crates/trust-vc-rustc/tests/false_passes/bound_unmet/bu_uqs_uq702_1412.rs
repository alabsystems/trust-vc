verus!{
impl U<B> for Z {
    proof fn lm0(&self) { }
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    proof fn dd(&self) where T: Tr { self.lm0(); }
}
impl Q for B { }
pub trait Q { }
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
pub trait Tr { }
pub struct Z { pub z: u8 }
impl U<B> for B {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
impl U<B> for A {
    proof fn lm0(&self) { }
}
} // verus!
