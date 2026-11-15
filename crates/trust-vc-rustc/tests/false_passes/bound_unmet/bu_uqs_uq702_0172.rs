verus!{
impl Tr for B { }
impl U<B> for A {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
}
pub struct B { pub b: u8 }
pub trait Tr { }
impl Q for B { }
pub trait Q { }
pub struct Z { pub z: u8 }
impl U<A> for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where T: Tr ensures self.mm() == 2;
    proof fn dd(&self) where T: Tr { self.lm0(); }
}
} // verus!
