verus!{
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub trait Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm(&self) where T: Tr ensures self.mm() == 2;
}
impl U<B> for A {
    proof fn lm(&self) { }
}
} // verus!
